module MaquinaBebidasQuentes

----------------------------------------------------------
--		   ASSINATURAS	            --
----------------------------------------------------------

abstract sig BotaoCancelar{
}

sig BotaoDeCancelamentoAtivado extends BotaoCancelar{
}

sig BotaoDeCancelamentoDesativado extends BotaoCancelar{
}

sig Maquina{
    bebida: lone Bebida,
    botaoDeCancelamento: set BotaoCancelar
}

abstract sig Bebida{
   tamanho: one Tamanho,
   adocamento: lone Adocamento,
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

fact maquinaNaoRequerBebida{
   all m: Maquina | #(m.bebida) >=0
}

fact bebidaRequerMaquina{
   all b : Bebida | #(b.~bebida) = 1
}

fact adicionalRequerBebida{
   all a: Adicional | #(a.~adicional) > 0
}

fact botaoCancelarRequerMaquina{
   all bt: BotaoCancelar | #(bt.~botaoDeCancelamento) = 1
}

fact botaoCancelarAtivadoRequerBebida{
   all bt: BotaoDeCancelamentoAtivado | #(bt.~botaoDeCancelamento.bebida) > 0 
}

fact botaoCancelarPossuiUnicaInstancia{
  all m: Maquina | #(m.botaoDeCancelamento) = 1
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
run show for 10

-----------------------------------------------------------
--			ASSERTS			 --
-----------------------------------------------------------

assert testMaquinaComOuSemBebida{
  all b: Bebida | #(b) = 0
}

assert testBebidaComVariasAdicoesDeLeite{
  some b: Bebida | #(b.adicional) > 1
}


-----------------------------------------------------------
--			CHECKS			 --
-----------------------------------------------------------

check testBebidaComVariasAdicoesDeLeite for 1

check  testMaquinaComOuSemBebida for 10






