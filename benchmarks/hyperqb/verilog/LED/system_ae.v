module led_fsm(input clock, input reset, output [4:0] LEDs);
	reg [4:0] LEDs = 5'b 10101;
	reg up = 1'b 0;
	reg on = 1'b 1;
	reg [2:0] led_state = 3'b 010; // 1: 1, 2: 1+2, 3: 1+2+3, 4: 1+2+3+4, 5: 1+2+3+4+5, 0+6+7 wie 1.

	always @(posedge clock)
	begin
	    if (reset) begin
	        LEDs <= 5'b 10101;
	        led_state <= 3'b 010;
	        on <= 1'b 1;
	        up <= 1'b 0;
	    end
	    else begin
	        if (on) begin
	            LEDs <= 5'b 00000;
	            on <= 1'b 0;
	        end
	        else begin
	            case (led_state)
	                3'b 010: begin
	                    if (up) begin
	                        LEDs <= 5'b 00111;
	                        led_state <= 3'b 011;
	                        up <= 1'b 1;
	                    end
	                    else begin
	                        LEDs <= 5'b 00001;
	                        led_state <= 3'b 001;
	                        up <= 1'b 1;
	                    end
	                end
	                3'b 011: begin
	                    if (up) begin
	                        LEDs <= 5'b 01111;
	                        led_state <= 3'b 100;
	                        up <= 1'b 1;
	                    end
	                    else begin
	                        LEDs <= 5'b 00011;
	                        led_state <= 3'b 010;
	                        up <= 1'b 0;
	                    end
	                end
	                3'b 100: begin 
	                    if (up) begin
	                        LEDs <= 5'b 11111;
	                        led_state <= 3'b 101;
	                        up <= 1'b 0;
	                    end
	                    else begin
	                        LEDs <= 5'b 00111;
	                        led_state <= 3'b 011;
	                        up <= 1'b 0;
	                    end
	                end
	                3'b 101: begin 
	                    if (up) begin
	                        LEDs <= 5'b 00000;
	                        led_state <= 3'b 000;
	                        up <= 1'b 1;
	                    end
	                    else begin
	                        LEDs <= 5'b 01111;
	                        led_state <= 3'b 100;
	                        up <= 1'b 0;
	                    end
	                end
	                default: begin // 000, 001, 110, 111
	                    if (up) begin
	                        LEDs <= 5'b 00011;
	                        led_state <= 3'b 010;
	                        up <= 1'b 1;
	                    end
	                    else begin
	                        LEDs <= 5'b 00000;
	                        led_state <= 3'b 000;
	                        up <= 1'b 1;
	                    end
	                end
	            endcase
	            on <= 1'b 1;
	        end
	    end
	end
endmodule