module
public import SerrePositivity.KST.SConstruction.ZeroSourceThetaEquivalence
public import SerrePositivity.KST.SConstruction.McCarthyRhoFiberHomotopy
public import SerrePositivity.KST.SConstruction.ArTimeCoordinates

/-! # ρ の終端から θ の入力空間への持ち上げ
概要：ρ の終端の各 gapped 図式を固定零 subobject の全空間へ自然に持ち上げる。
方針：終端の subobject の厳密な定値性で頂点 fiber に入れる。
規約：元の cofiber 図式を変更しない。使われ方：第二の θ の可変時刻での評価。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：ρ の終端の実図式を指定零 subobject の空間へ持ち上げる。
方針：最後の対角零対象への厳密な等号を頂点 fiber の条件にする。
規約：全 Ar 単体で同じ持ち上げ。使われ方：θ の入力図式。 -/
def mcCarthyThetaDiagram (X : StableModel.{u}) {m n : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) (e : (cofiberSubobjectLeftFiber X a) _⦋n⦌) :
    arNerve n ⟶ zeroSourceCofibers (objectSLastDiagonalZeroVertex a) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _
    (mcCarthyFiberDiagram X a ((mcCarthyRhoTerminal X a).app (Opposite.op ⦋n⦌) e))
      (mcCarthyRhoTerminal_source X a e)

/-- 概要：θ の入力図式を含めると元の ρ の終端の実図式。
方針：頂点 fiber の持ち上げの包含の式。
規約：図式全体の等号。使われ方：gapped 性と両端の照合。 -/
lemma mcCarthyThetaDiagram_ι (X : StableModel.{u}) {m n : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) (e : (cofiberSubobjectLeftFiber X a) _⦋n⦌) :
    mcCarthyThetaDiagram X a e ≫ zeroSourceCofibersι (objectSLastDiagonalZeroVertex a) =
      mcCarthyFiberDiagram X a ((mcCarthyRhoTerminal X a).app (Opposite.op ⦋n⦌) e) := rfl

/-- 概要：θ の入力図式は全ての面・退化による Ar の前合成と可換。
方針：頂点 fiber の包含後に ρ の終端と左 fiber の射影の自然性を使う。
規約：持ち上げの証明の選択には依存しない。使われ方：θ の単体的自然性。 -/
lemma mcCarthyThetaDiagram_map (X : StableModel.{u}) {m n l : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) (e : (cofiberSubobjectLeftFiber X a) _⦋n⦌)
    (σ : ⦋l⦌ ⟶ ⦋n⦌) :
    mcCarthyThetaDiagram X a ((cofiberSubobjectLeftFiber X a).map σ.op e) =
      arNerveMap σ.toOrderHom ≫ mcCarthyThetaDiagram X a e := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext _ _
  change _ ≫ zeroSourceCofibersι (objectSLastDiagonalZeroVertex a) =
    _ ≫ zeroSourceCofibersι (objectSLastDiagonalZeroVertex a)
  rw [mcCarthyThetaDiagram_ι, Category.assoc, mcCarthyThetaDiagram_ι]
  have ht := ConcreteCategory.congr_hom ((mcCarthyRhoTerminal X a).naturality σ.op) e
  change (mcCarthyRhoTerminal X a).app (Opposite.op ⦋l⦌)
      ((cofiberSubobjectLeftFiber X a).map σ.op e) =
    (cofiberSubobjectLeftFiber X a).map σ.op
      ((mcCarthyRhoTerminal X a).app (Opposite.op ⦋n⦌) e) at ht
  rw [ht, mcCarthyFiberDiagram_map]

/-- 概要：θ の入力を元に含めた図式は gapped。
方針：元の左 fiber の射影の gapped 図式そのものであることを使う。
規約：入力空間の安定性は要求しない。使われ方：可変時刻の gapped 性の輸送。 -/
lemma mcCarthyThetaDiagram_isGapped (X : StableModel.{u}) {m n : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) (e : (cofiberSubobjectLeftFiber X a) _⦋n⦌) :
    IsGapped (mcCarthyThetaDiagram X a e ≫
      zeroSourceCofibersι (objectSLastDiagonalZeroVertex a)) := by
  rw [mcCarthyThetaDiagram_ι]
  exact gappedDiagram_isGapped _

end SerrePositivity.KST.SConstruction
