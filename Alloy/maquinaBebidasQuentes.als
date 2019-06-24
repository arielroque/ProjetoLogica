open util/integer
module MaquinaBebidasQuentes
----------------------------------------------------------
--		   ASSINATURAS	            --
----------------------------------------------------------
sig Maquina{
    bebida: lone Bebida,
    botaoDeCancelamento: set BotaoCancelar,
    valorInserido: one Int,
    troco: one Int,
    status: one Status
    
}

abstract sig Status{}

sig PedidoFinalizado extends Status{}
sig PedidoEmFalta extends Status{}
sig PedidoCancelado extends Status{}


abstract sig BotaoCancelar{}

sig BotaoDeCancelamentoAtivado extends BotaoCancelar{}

sig BotaoDeCancelamentoDesativado extends BotaoCancelar{}

abstract sig Bebida{
   tamanho: one Tamanho,
   adocamento: lone Adocamento,
   adicional: set Adicional
}

sig Cafe extends Bebida{}

sig ChocolateQuente extends Bebida{}

sig Cha extends Bebida{}

abstract sig Tamanho{}

sig TamanhoGrande extends Tamanho{}

sig TamanhoPequeno extends Tamanho{}

abstract sig Adicional{}

sig Leite extends Adicional{}

abstract sig Adocamento {}

sig Acucar extends Adocamento{}

sig Adocante extends Adocamento{}
----------------------------------------------------------
--			FATOS		       --
----------------------------------------------------------
fact maquinaExiste{
  all m: Maquina | #(m) > 0
}
fact maquinaNaoRequerBebida{
   all m: Maquina | #(m.bebida) >= 0
}

fact valorInseridoDeveSerPositivo{
    all m: Maquina | m.valorInserido >= 100
}

fact valorInseridoPermitido{
    all m: Maquina | moedasPermitidas[m]
}

fact bebidaRequerMaquina{
   all b : Bebida | #(b.~bebida) > 0
}

fact adicionalRequerBebida{
   all a: Adicional | #(a.~adicional) > 0
}

fact adicionalDependeDoValorInserido{
  all  b: Bebida | #(b.adicional) > -1 && #(b.adicional) < getQuantMaximaAdicional[b.~bebida]
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

fact statusRequerMaquina{
  all s: Status | #(s.~status) > 0  
}

fact trocoDaMaquina{
  all m: Maquina | trocoMoeda50[m]
  all m: Maquina | trocoMoeda25[m]
  all m: Maquina | trocoVazio[m]
}

fact trocoComBebidaIndisponivel{
  all m: Maquina | bebidaIndisponivel[m]
}

fact statusPedido{
  all m : Maquina | bebidaFinalizada[m]
  all m : Maquina | bebidaCancelada[m]
  all m : Maquina | bebidaEmFalta[m]
}


----------------------------------------------------------
--			PREDICADOS	       --
----------------------------------------------------------
pred moedasPermitidas[m: Maquina]{
    rem[m.valorInserido,100] = 0 || rem[m.valorInserido,25] = 0 || rem[m.valorInserido,50] = 0
}

pred trocoMoeda50[m : Maquina]{
 //m.troco = getTroco[m]
  getTroco[m] > 49 => m.troco = 50 
}

pred trocoMoeda25[m : Maquina]{
 //m.troco = getTroco[m]
  getTroco[m] > 24 && getTroco[m] < 50 => m.troco = 25
}
pred trocoVazio[m : Maquina]{
 //m.troco = getTroco[m]
  getTroco[m] < 25 => m.troco = 0 || m.botaoDeCancelamento = BotaoDeCancelamentoAtivado => m.troco = 0 
}

pred bebidaIndisponivel[m : Maquina]{
  #(m.bebida) = 0 => m.troco = m.valorInserido
}

pred bebidaFinalizada[m: Maquina]{
  #(m.bebida) > 0 && m.botaoDeCancelamento = BotaoDeCancelamentoDesativado  => m.status = PedidoFinalizado
}

pred bebidaCancelada[m: Maquina]{
  m.botaoDeCancelamento = BotaoDeCancelamentoAtivado => m.status = PedidoCancelado && m.troco = 0
}

pred bebidaEmFalta[m: Maquina]{
 #(m.bebida) = 0 => m.status = PedidoEmFalta
}


----------------------------------------------------------
--			FUNCOES		       --
----------------------------------------------------------

fun getValorInseridoMenosBebida[m : Maquina]: Int{
    minus[m.valorInserido,100]
}

fun getQuantMaximaAdicional[m: Maquina] : Int{
   div[getValorInseridoMenosBebida[m],50]
}

fun getValorAdicional[m: Maquina] : Int{
   mul[#(m.bebida.adicional),50]
}

fun getTroco[m: Maquina]: Int{
   minus[m.valorInserido,plus[100,getValorAdicional[m]]]
}


----------------------------------------------------------
--		        RUN		       --
----------------------------------------------------------
pred show[] {}
run show for 10 Int

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






