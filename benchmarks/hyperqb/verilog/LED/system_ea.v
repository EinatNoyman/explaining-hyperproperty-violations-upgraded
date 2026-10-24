module led_fsm(
    input  clock,
    input  reset,
    output       LED0,       // separate bit output
    output [3:0] LEDs_hi     // upper four bits output
);
    // separate state registers
    reg        LED0_r    = 1'b1;
    reg [3:0]  LEDs_hi_r = 4'b0101;

    reg        up    = 1'b0;
    reg        on    = 1'b1;
    reg [2:0]  led_state = 3'b010;

    // connect regs to ports
    assign LED0    = LED0_r;
    assign LEDs_hi = LEDs_hi_r;

    always @(posedge clock) begin
        if (reset) begin
            LED0_r    <= 1'b1;
            LEDs_hi_r <= 4'b0101;
            led_state     <= 3'b010;
            on        <= 1'b1;
            up        <= 1'b0;
        end else begin
            if (on) begin
                LED0_r    <= 1'b0;
                LEDs_hi_r <= 4'b0000;
                on        <= 1'b0;
            end else begin
                case (led_state)
                    3'b010: begin
                        if (up) begin
                            LED0_r    <= 1'b1;
                            LEDs_hi_r <= 4'b0011;
                            led_state     <= 3'b011;
                            up        <= 1'b1;
                        end else begin
                            LED0_r    <= 1'b1;
                            LEDs_hi_r <= 4'b0000;
                            led_state     <= 3'b001;
                            up        <= 1'b1;
                        end
                    end
                    3'b011: begin
                        if (up) begin
                            LED0_r    <= 1'b1;
                            LEDs_hi_r <= 4'b0111;
                            led_state     <= 3'b100;
                            up        <= 1'b1;
                        end else begin
                            LED0_r    <= 1'b1;
                            LEDs_hi_r <= 4'b0011;
                            led_state     <= 3'b010;
                            up        <= 1'b0;
                        end
                    end
                    3'b100: begin
                        if (up) begin
                            LED0_r    <= 1'b1;
                            LEDs_hi_r <= 4'b1111;
                            led_state     <= 3'b101;
                            up        <= 1'b0;
                        end else begin
                            LED0_r    <= 1'b1;
                            LEDs_hi_r <= 4'b0111;
                            led_state     <= 3'b011;
                            up        <= 1'b0;
                        end
                    end
                    3'b101: begin
                        if (up) begin
                            LED0_r    <= 1'b0;
                            LEDs_hi_r <= 4'b0000;
                            led_state     <= 3'b000;
                            up        <= 1'b1;
                        end else begin
                            LED0_r    <= 1'b1;
                            LEDs_hi_r <= 4'b1111;
                            led_state     <= 3'b100;
                            up        <= 1'b0;
                        end
                    end
                    default: begin
                        if (up) begin
                            LED0_r    <= 1'b1;
                            LEDs_hi_r <= 4'b0011;
                            led_state     <= 3'b010;
                            up        <= 1'b1;
                        end else begin
                            LED0_r    <= 1'b0;
                            LEDs_hi_r <= 4'b0000;
                            led_state     <= 3'b000;
                            up        <= 1'b1;
                        end
                    end
                endcase
                on <= 1'b1;
            end
        end
    end
endmodule
