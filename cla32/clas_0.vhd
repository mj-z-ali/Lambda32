library IEEE;
use IEEE.std_logic_1164.all;


entity clas_0 is 
	
    port (
    	a, b, ci : in bit;
      	s : out bit);
        
end entity clas_0;


architecture clas_0_arc of clas_0 is
	    
begin

    s <= (a and b and ci) or 
    	 (a and not b and not ci) or 
    	 (not a and b and not ci) or 
    	 (not a and not b and ci);

end architecture clas_0_arc;
        
        
    	  