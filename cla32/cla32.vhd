library IEEE;
use IEEE.std_logic_1164.all;


entity cla32 is 
	
    port (
    	a, b : in bit_vector(31 downto 0);
      	cin	 : in bit;
        s_old : in bit_vector(31 downto 0);
        co_old : in bit;
        p_state : in bit_vector(15 downto 0);
        s	 : out bit_vector(31 downto 0);
        cout : out bit);
        
end entity cla32;


architecture cla32_arc of cla32 is
	
    signal a_1, a_0, b_1, b_0, ci : bit;
    signal co, s_1, s_0 : bit;
    
begin

	clas_0_inst : entity work.clas_0(clas_0_arc) 
    port map (
    		a => a_0,
            b => b_0,
            ci => ci,
            s => s_0);
            
    clas_1_inst : entity work.clas_1(clas_1_arc)
    port map (
    		a_0 => a_0,
            a_1 => a_1,
            b_0 => b_0,
            b_1 => b_1,
            ci => ci,
            s => s_1);
 
 	claco_inst : entity work.claco(claco_arc)
    port map (
    		a_0 => a_0,
            a_1 => a_1,
            b_0 => b_0,
            b_1 => b_1,
            ci => ci,
            co => co);
   	
    a_0 <= 	(p_state(0) and a(0)) or
            (p_state(1) and a(2)) or
            (p_state(2) and a(4)) or
            (p_state(3) and a(6)) or
            (p_state(4) and a(8)) or
            (p_state(5) and a(10)) or
            (p_state(6) and a(12)) or
            (p_state(7) and a(14)) or
            (p_state(8) and a(16)) or
            (p_state(9) and a(18)) or
            (p_state(10) and a(20)) or
            (p_state(11) and a(22)) or
            (p_state(12) and a(24)) or
            (p_state(13) and a(26)) or
            (p_state(14) and a(28)) or
            (p_state(15) and a(30));


    a_1 <= 	(p_state(0) and a(1)) or
            (p_state(1) and a(3)) or
            (p_state(2) and a(5)) or
            (p_state(3) and a(7)) or
            (p_state(4) and a(9)) or
            (p_state(5) and a(11)) or
            (p_state(6) and a(13)) or
            (p_state(7) and a(15)) or
            (p_state(8) and a(17)) or
            (p_state(9) and a(19)) or
            (p_state(10) and a(21)) or
            (p_state(11) and a(23)) or
            (p_state(12) and a(25)) or
            (p_state(13) and a(27)) or
            (p_state(14) and a(29)) or
            (p_state(15) and a(31));

    b_0 <= 	(p_state(0) and b(0)) or
            (p_state(1) and b(2)) or
            (p_state(2) and b(4)) or
            (p_state(3) and b(6)) or
            (p_state(4) and b(8)) or
            (p_state(5) and b(10)) or
            (p_state(6) and b(12)) or
            (p_state(7) and b(14)) or
            (p_state(8) and b(16)) or
            (p_state(9) and b(18)) or
            (p_state(10) and b(20)) or
            (p_state(11) and b(22)) or
            (p_state(12) and b(24)) or
            (p_state(13) and b(26)) or
            (p_state(14) and b(28)) or
            (p_state(15) and b(30));


    b_1 <= 	(p_state(0) and b(1)) or
            (p_state(1) and b(3)) or
            (p_state(2) and b(5)) or
            (p_state(3) and b(7)) or
            (p_state(4) and b(9)) or
            (p_state(5) and b(11)) or
            (p_state(6) and b(13)) or
            (p_state(7) and b(15)) or
            (p_state(8) and b(17)) or
            (p_state(9) and b(19)) or
            (p_state(10) and b(21)) or
            (p_state(11) and b(23)) or
            (p_state(12) and b(25)) or
            (p_state(13) and b(27)) or
            (p_state(14) and b(29)) or
            (p_state(15) and b(31));       

	ci <=   (p_state(0) and cin) or
    		(not p_state(0) and co_old);
            
 	s(0) <=  (p_state(0) and s_0) or 
		 	 (not p_state(0) and s_old(0));
			
    s(1) <=  (p_state(0) and s_1) or 
             (not p_state(0) and s_old(1));

    s(2) <=  (p_state(1) and s_0) or 
             (not p_state(1) and s_old(2));

    s(3) <=  (p_state(1) and s_1) or 
             (not p_state(1) and s_old(3));

    s(4) <=  (p_state(2) and s_0) or 
             (not p_state(2) and s_old(4));

    s(5) <=  (p_state(2) and s_1) or 
             (not p_state(2) and s_old(5));

    s(6) <=  (p_state(3) and s_0) or 
             (not p_state(3) and s_old(6));

    s(7) <=  (p_state(3) and s_1) or 
             (not p_state(3) and s_old(7));

    s(8) <=  (p_state(4) and s_0) or 
             (not p_state(4) and s_old(8));

    s(9) <=  (p_state(4) and s_1) or 
             (not p_state(4) and s_old(9));

    s(10) <=  (p_state(5) and s_0) or 
              (not p_state(5) and s_old(10));

    s(11) <=  (p_state(5) and s_1) or 
              (not p_state(5) and s_old(11));

    s(12) <=  (p_state(6) and s_0) or 
              (not p_state(6) and s_old(12));

    s(13) <=  (p_state(6) and s_1) or 
              (not p_state(6) and s_old(13));

    s(14) <=  (p_state(7) and s_0) or 
              (not p_state(7) and s_old(14));

    s(15) <=  (p_state(7) and s_1) or 
              (not p_state(7) and s_old(15));

    s(16) <=  (p_state(8) and s_0) or 
              (not p_state(8) and s_old(16));

    s(17) <=  (p_state(8) and s_1) or 
              (not p_state(8) and s_old(17));

    s(18) <=  (p_state(9) and s_0) or 
              (not p_state(9) and s_old(18));

    s(19) <=  (p_state(9) and s_1) or 
              (not p_state(9) and s_old(19));

    s(20) <=  (p_state(10) and s_0) or 
              (not p_state(10) and s_old(20));

    s(21) <=  (p_state(10) and s_1) or 
              (not p_state(10) and s_old(21));

    s(22) <=  (p_state(11) and s_0) or 
              (not p_state(11) and s_old(22));

    s(23) <=  (p_state(11) and s_1) or 
              (not p_state(11) and s_old(23));

    s(24) <=  (p_state(12) and s_0) or 
              (not p_state(12) and s_old(24));

    s(25) <=  (p_state(12) and s_1) or 
              (not p_state(12) and s_old(25));

    s(26) <=  (p_state(13) and s_0) or 
              (not p_state(13) and s_old(26));

    s(27) <=  (p_state(13) and s_1) or 
              (not p_state(13) and s_old(27));

    s(28) <=  (p_state(14) and s_0) or 
              (not p_state(14) and s_old(28));

    s(29) <=  (p_state(14) and s_1) or 
              (not p_state(14) and s_old(29));

    s(30) <=  (p_state(15) and s_0) or 
              (not p_state(15) and s_old(30));

    s(31) <=  (p_state(15) and s_1) or 
              (not p_state(15) and s_old(31));  

      
   	cout <= co;
  

end architecture cla32_arc;
        
        
    	  