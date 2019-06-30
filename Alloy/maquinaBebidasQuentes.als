open util/integer
module MaquinaBebidasQuentes
----------------------------------------------------------
--		   ASSINATURAS	            --
----------------------------------------------------------
one sig Maquina{
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
   valor: one Int,
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
fact valorInseridoDeveSerPositivo{
    all m: Maquina | m.valorInserido >= 50
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
  all  m: Maquina  | #(m.bebida.adicional) >= 0 && #(m.bebida.adicional) <= getQuantMaximaAdicional[m]
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
  all s: Status | #(s.~status) = 1  
}

fact precoBebida{
  all m: Maquina | precoBebidaMenor100[m]
  all m: Maquina | precoBebidaMaior100[m]
  all m: Maquina | tamanhoGrande[m.bebida]
  all m: Maquina | tamanhoPequeno[m.bebida]
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

pred precoBebidaMaior100[m: Maquina]{
  (getValorInserido[m] > 99) => (#getBebida[m] = 0) || (getValorBebida[m.bebida] = 100) || (getValorBebida[m.bebida] = 50)
} 

pred precoBebidaMenor100[m: Maquina]{
  (getValorInserido[m] > 49) && (getValorInserido[m] < 100) => (#getBebida[m] = 0) || (getValorBebida[m.bebida] = 50)
 
}

pred tamanhoGrande[b: Bebida]{
     (getValorBebida[b] = 100) => (#getTamanhoGrande[b]) > 0
}

pred tamanhoPequeno[b: Bebida]{
     (getValorBebida[b] = 50) => (#getTamanhoPequeno[b]) > 0
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
fun getTamanhoGrande [b: Bebida]: set TamanhoGrande{
    TamanhoGrande & b.tamanho
}

fun getTamanhoPequeno [b: Bebida]: set TamanhoPequeno{
   TamanhoPequeno & b.tamanho
}

fun getValorInserido[m: Maquina]: Int{
   m.valorInserido
}

fun getValorBebida[b: Bebida]: Int{
   b.valor
}

fun getValorInseridoMenosBebida[m : Maquina]: Int{
    minus[getValorInserido[m],getValorBebida[m.bebida]]
}

fun getQuantMaximaAdicional[m: Maquina] : Int{
   div[getValorInseridoMenosBebida[m],50]
}

fun getValorAdicional[m: Maquina] : Int{
   mul[#(m.bebida.adicional),50]
}

fun getBebida [m: Maquina]: set Bebida{
    m.bebida & Bebida
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

fun getValorGasto[m: Maquina]: Int{
   plus[getValorBebida[m.bebida],getValorAdicional[m]]
}

fun calcularTroco[m: Maquina]: Int{
   minus[getValorInserido[m],getValorGasto[m]]
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
  all m: Maquina | (#getBebida[m] = 0) || (#getBebida[m] = 1) 
}

assert testBebidaComOuSemAdocamento{
  all b: Bebida | (#b.adocamento >= 0)
}

assert testBebidaComOuSemAdicional{
  all b: Bebida | (#b.adicional >= 0)
}

assert testTrocoMaquinaSemBebida{
  all m: Maquina | (#getBebida[m] = 0) => (getTroco[m] = getValorInserido[m])
}

assert testTrocoBebidaCancelada{
 all m: Maquina | (#getBotaoAtivado[m] > 0) => (getTroco[m] = 0)
}

assert testValorInseridoMaiorIgualGasto{
 all m: Maquina | (getValorInserido[m] >= getValorGasto[m])
}

-----------------------------------------------------------
--			CHECKS			 --
-----------------------------------------------------------
check testMaquinaComOuSemBebida for 10 int
check testBebidaComOuSemAdicional for 10 int
check testBebidaComOuSemAdocamento for 10 int
check testTrocoMaquinaSemBebida for 10 int
check testTrocoBebidaCancelada for 10 int
check testValorInseridoMaiorIgualGasto for 10 int






