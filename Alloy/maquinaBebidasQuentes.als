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

fact trocoMaquina{
  all m: Maquina | trocoMoeda50[m]
  all m: Maquina | trocoMoeda25[m]
  all m: Maquina | trocoVazio[m]
}

fact statusPedido{
   all m: Maquina | statusCancelado[m]
   all m: Maquina | statusEmFalta[m]
   all m: Maquina | statusFinalizado[m]
}

----------------------------------------------------------
--			PREDICADOS	       --
----------------------------------------------------------
pred moedasPermitidas[m: Maquina]{
    rem[m.valorInserido,100] = 0 || rem[m.valorInserido,25] = 0 || rem[m.valorInserido,50] = 0
}

pred trocoMoeda50[m : Maquina]{
 (calcularTroco[m] > 49) => (getTroco[m] = 50) 
}

pred trocoMoeda25[m : Maquina]{
  (calcularTroco[m]) > 24 && (calcularTroco[m]) < 50 =>  (getTroco[m] = 25)
}
pred trocoVazio[m : Maquina]{
  (calcularTroco[m] < 25) => (getTroco[m] = 0) 
}

pred statusCancelado [m: Maquina] {
	(#getBotaoAtivado[m] > 0) => (#getPedidoCancelado[m] > 0) &&  (getTroco[m] = 0)
}

pred statusEmFalta [m: Maquina] {
	(#getBebida[m] = 0) => (#getPedidoEmFalta[m]) > 0  &&  (getTroco[m] = m.valorInserido)
}

pred statusFinalizado [m : Maquina]{
   (#getBotaoDesativado[m] > 0) && (#getBebida[m] > 0) => (#getPedidoFinalizado[m]) > 0
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

fun getBebida [m: Maquina]: set Bebida{
    m.bebida
}

fun getTroco[m:Maquina]: Int{
   m.troco
}

fun getBotaoAtivado [m: Maquina] : set BotaoDeCancelamentoAtivado {
    BotaoDeCancelamentoAtivado & m.botaoDeCancelamento
}

fun getBotaoDesativado [m: Maquina] : set BotaoDeCancelamentoDesativado {
    BotaoDeCancelamentoDesativado & m.botaoDeCancelamento
}

fun getPedidoCancelado [m: Maquina] : set PedidoCancelado {
    PedidoCancelado & m.status
}

fun getPedidoEmFalta [m: Maquina] : set PedidoEmFalta{
   PedidoEmFalta & m.status
}

fun getPedidoFinalizado [m: Maquina] : set PedidoFinalizado{
   PedidoFinalizado & m.status
}

fun calcularTroco[m: Maquina]: Int{
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






