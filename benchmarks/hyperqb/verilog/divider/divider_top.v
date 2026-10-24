`timescale 1ns/1ps
`default_nettype none

// Standard-execution harness for divider:
// - Internal POR (no external reset); initial block uses only constants.
// - CPU-like sequencer: present A, wait for ack; present B, wait for ack; wait for result.
// - Keep z_ack low so z_stb stays visible; expose a sticky done and latency.
// - Operands from a small LUT (selectors a_sel/b_sel).
module divider_top (
  input  wire        clk,

  // Selectors for valid LUT operands (leave unconstrained for ∀ over values)
  input  wire [1:0]  a_sel,
  input  wire [1:0]  b_sel,

  // Observability of what we drive
  output wire [31:0] a_i_o,
  output wire [31:0] b_i_o,
  output wire        a_stb_o,
  output wire        b_stb_o,
  output wire        z_ack_o,

  // DUT outputs
  output wire [31:0] z_o,
  output wire        z_stb_o,
  output wire        a_ack_o,
  output wire        b_ack_o,

  // Analysis helpers
  output wire        started_o,   // 1-cycle pulse when both operands are accepted
  output wire        done_o,      // sticky high once result is ready
  output wire [15:0] latency_o    // cycles from start→done (saturating)
);

  // ---------------------------
  // Operand LUT (edit/extend)
  // ---------------------------
  function [31:0] lut_val;
    input [1:0] idx;
    case (idx)
      2'd0: lut_val = 32'h3f80_0000; // 1.0
      2'd1: lut_val = 32'h4000_0000; // 2.0
      2'd2: lut_val = 32'h4040_0000; // 3.0
      2'd3: lut_val = 32'h3f00_0000; // 0.5
      default: lut_val = 32'h3f80_0000;
    endcase
  endfunction

  // ---------------------------
  // Internal power-on reset (POR)
  // ---------------------------
  (* keep = "true" *) reg        rst_q;
  (* keep = "true" *) reg  [1:0] por_cnt;

  // ---------------------------
  // Driver state machine
  // ---------------------------
  localparam [2:0]
    D_POR      = 3'd0,
    D_LOAD     = 3'd1,  // load selected operands into regs
    D_SEND_A   = 3'd2,  // assert A strobe until ack
    D_SEND_B   = 3'd3,  // assert B strobe until ack
    D_WAIT_Z   = 3'd4,  // wait for output_z_stb
    D_HOLD     = 3'd5;  // hold result visible; sticky done stays 1

  (* keep = "true" *) reg [2:0] drv_state_q;

  // ---------------------------
  // Environment → DUT (registered)
  // ---------------------------
  (* keep = "true" *) reg  [31:0] input_a_q, input_b_q;
  (* keep = "true" *) reg         input_a_stb_q, input_b_stb_q;
  (* keep = "true" *) reg         output_z_ack_q;

  assign a_i_o    = input_a_q;
  assign b_i_o    = input_b_q;
  assign a_stb_o  = input_a_stb_q;
  assign b_stb_o  = input_b_stb_q;
  assign z_ack_o  = output_z_ack_q;

  // ---------------------------
  // DUT outputs
  // ---------------------------
  wire [31:0] output_z;
  wire        output_z_stb;
  wire        input_a_ack;
  wire        input_b_ack;

  assign z_o     = output_z;
  assign z_stb_o = output_z_stb;
  assign a_ack_o = input_a_ack;
  assign b_ack_o = input_b_ack;

  // ---------------------------
  // Handshake/latency helpers
  // ---------------------------
  (* keep = "true" *) reg got_a_q, got_b_q;   // latched when each operand is accepted
  (* keep = "true" *) reg started_q;          // 1-cycle pulse when both got_* become 1
  (* keep = "true" *) reg done_q;             // sticky once output_z_stb is seen
  (* keep = "true" *) reg [15:0] latency_q;   // counts cycles from start until done (sat)

  assign started_o = started_q;
  assign done_o    = done_q;
  assign latency_o = latency_q;

  // ---------------------------
  // Instance of the divider (rst_q only)
  // ---------------------------
  divider dut (
    .input_a      (input_a_q),
    .input_b      (input_b_q),
    .input_a_stb  (input_a_stb_q),
    .input_b_stb  (input_b_stb_q),
    .output_z_ack (output_z_ack_q),
    .clk          (clk),
    .rst          (rst_q),
    .output_z     (output_z),
    .output_z_stb (output_z_stb),
    .input_a_ack  (input_a_ack),
    .input_b_ack  (input_b_ack)
  );

  // ---------------------------
  // Deterministic initial state (constants only)
  // ---------------------------
  initial begin
    rst_q          = 1'b1;
    por_cnt        = 2'd0;

    drv_state_q    = D_POR;

    input_a_q      = 32'h0000_0000;
    input_b_q      = 32'h0000_0000;
    input_a_stb_q  = 1'b0;
    input_b_stb_q  = 1'b0;
    output_z_ack_q = 1'b0;     // keep 0 so z_stb remains visible

    got_a_q        = 1'b0;
    got_b_q        = 1'b0;
    started_q      = 1'b0;
    done_q         = 1'b0;
    latency_q      = 16'd0;
  end

  // ---------------------------
  // Sequencer (similar procedure to your file_writer flow)
  // ---------------------------
  always @(posedge clk) begin
    // Internal POR: hold reset for two cycles, then release
    if (rst_q) begin
      por_cnt    <= por_cnt + 2'd1;
      if (por_cnt == 2'd1) begin
        rst_q       <= 1'b0;
        drv_state_q <= D_LOAD;
      end
      // keep interface quiescent in POR
      input_a_stb_q  <= 1'b0;
      input_b_stb_q  <= 1'b0;
      output_z_ack_q <= 1'b0;
      got_a_q        <= 1'b0;
      got_b_q        <= 1'b0;
      started_q      <= 1'b0;
      done_q         <= 1'b0;
      latency_q      <= 16'd0;
    end else begin
      // defaults each cycle
      started_q <= 1'b0;       // pulse
      output_z_ack_q <= 1'b0;  // never ack; keep z_stb visible

      case (drv_state_q)
        D_LOAD: begin
          // Load selected operands (like your CPU loading a register)
          input_a_q   <= lut_val(a_sel);
          input_b_q   <= lut_val(b_sel);
          input_a_stb_q <= 1'b0;
          input_b_stb_q <= 1'b0;
          got_a_q     <= 1'b0;
          got_b_q     <= 1'b0;
          done_q      <= 1'b0;
          latency_q   <= 16'd0;
          drv_state_q <= D_SEND_A;
        end

        D_SEND_A: begin
          // Present A until the DUT acknowledges (mirrors "read a" then continue)
          input_a_stb_q <= 1'b1;
          if (input_a_ack) begin
            input_a_stb_q <= 1'b0;
            got_a_q       <= 1'b1;
            drv_state_q   <= D_SEND_B;
          end
        end

        D_SEND_B: begin
          // Present B until the DUT acknowledges
          input_b_stb_q <= 1'b1;
          if (input_b_ack) begin
            input_b_stb_q <= 1'b0;
            got_b_q       <= 1'b1;
            started_q     <= 1'b1;     // both operands captured → start pulse
            drv_state_q   <= D_WAIT_Z;
          end
        end

        D_WAIT_Z: begin
          // Count latency until the result is ready
          if (!done_q && latency_q != 16'hFFFF)
            latency_q <= latency_q + 16'd1;

          if (output_z_stb) begin
            done_q      <= 1'b1;       // sticky
            drv_state_q <= D_HOLD;     // hold result visible (z_ack stays 0)
          end
        end

        D_HOLD: begin
          // Result is ready and visible; done stays high.
          done_q <= 1'b1;
          // If you want to issue another op automatically, jump back to D_LOAD here.
          // drv_state_q <= D_LOAD;
        end

        default: drv_state_q <= D_LOAD;
      endcase
    end
  end

endmodule

`default_nettype wire
