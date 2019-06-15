module MaquinaBebidasQuentes

----------------------------------------------------------
--		   ASSINATURAS	            --
----------------------------------------------------------


sig Maquina{
    bebida: lone Bebida
}

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
fact bebidaRequerMaquina{
   all b : Bebida | #(b.~bebida) = 1
}

fact adicionalRequerBebida{
   all a: Adicional | #(a.~adicional) > 0
}

fact tamanhoRequerBebida{
   all t: Tamanho | #(t.~tamanho) > 0
}

fact adocamentoRequerBebida{
  all a: Adocamento | #(a.~adocamento) > 0
}



----------------------------------------------------------
--		        RUN		       --
----------------------------------------------------------
pred show[] {}
run show for 15

-----------------------------------------------------------
--			ASSERTS			 --
-----------------------------------------------------------


-----------------------------------------------------------
--			CHECKS			 --
-----------------------------------------------------------






