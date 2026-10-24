module light(input clock, input up, output light_out);
    parameter [1:0] STATE_0 = 2'b00, STATE_1 = 2'b01, STATE_2 = 2'b10;
    parameter ON = 1'b1, OFF = 1'b0;
    
    reg l = OFF;
    reg [1:0] state123 = STATE_0;
    
    always @(posedge clock)
    begin
        case (state123)
            STATE_0: 
            begin
                if (up) begin
            		state123 <= STATE_1;
            		l <= ON;
                end else begin
                    state123 <= STATE_2;
                    l <= ON;
                end
            end
            
           	STATE_1:
            begin
                state123 <= STATE_0;
                l <= OFF;
            end
            
            STATE_2:
            begin
                state123 <= STATE_0;
                l <= OFF;
            end
        endcase
    end
    
    assign light_out = l;
endmodule