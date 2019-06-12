module MaquinaBebidasQuentes

----------------------------------------------------------
--		   ASSINATURAS	            --
----------------------------------------------------------

abstract sig Bebida{
   tamanho: one Tamanho,
   adocamento: one Adocamento,
   adicional: set Adicional
}

sig Cafe extends Bebida{
}
sig ChocolateQuente extends Bebida{
}
sig Cha extends Bebida{
}

abstract sig Tamanho{
}

sig TamanhoGrande extends Tamanho{
}
sig TamanhoPequeno extends Tamanho{
}


abstract sig Adicional{
}

sig Leite extends Adicional{
}

abstract sig Adocamento {
}

sig Acucar extends Adocamento{
}
sig Adocante extends Adocamento{
}


----------------------------------------------------------
--			FATOS		       --
----------------------------------------------------------



----------------------------------------------------------
--		        RUN		       --
----------------------------------------------------------
pred show[] {}
run show for 3

-----------------------------------------------------------
--			ASSERTS			 --
-----------------------------------------------------------
