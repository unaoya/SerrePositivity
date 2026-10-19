module
public import SerrePositivity.KST.SConstruction.McCarthyThetaDiagram

/-! # 第二の θ の object S 値の族
概要：ρ の終端の零 subobject 図式に大域的な θ を可変時刻で評価する。
方針：θ の点ごとの可逆性で gapped 性を移し、単一の選択の自然性で束ねる。
規約：各次数で別々の比較を選ばない。使われ方：左 fiber 内の第二のホモトピー。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：ρ の終端の図式に θ を時刻単体に沿って適用する。
方針：Ar の左端で時刻を読み、点ごとの可逆性で gapped 性を保証する。
規約：同じ大域的 θ を全単体に使う。使われ方：第二ホモトピーの各単体。 -/
def mcCarthyThetaObjectVertex (X : StableModel.{u}) {m n : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) (e : (cofiberSubobjectLeftFiber X a) _⦋n⦌)
    (τ : (Δ[1] : SSet.{u}) _⦋n⦌) : (objectSConstruction (cofiberDiagrams X.carrier)) _⦋n⦌ :=
  gappedObjectVertex
    (variableTimeImage (zeroSourceThetaHomotopy (objectSLastDiagonalZeroVertex a))
      (mcCarthyThetaDiagram X a e) (arTimeCoordinate τ))
    (zeroSourceTheta_variableTime_isGapped (objectSLastDiagonalZeroVertex a)
      (mcCarthyThetaDiagram X a e) (mcCarthyThetaDiagram_isGapped X a e) (arTimeCoordinate τ))

/-- 概要：θ の単体の実図式は大域的 θ の可変時刻での評価。
方針：gapped 図式の頂点との往復の式。
規約：実際の射の等号。使われ方：面・退化と端点の照合。 -/
lemma mcCarthyThetaObjectVertex_diagram (X : StableModel.{u}) {m n : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) (e : (cofiberSubobjectLeftFiber X a) _⦋n⦌)
    (τ : (Δ[1] : SSet.{u}) _⦋n⦌) :
    gappedDiagram (mcCarthyThetaObjectVertex X a e τ) =
      variableTimeImage (zeroSourceThetaHomotopy (objectSLastDiagonalZeroVertex a))
        (mcCarthyThetaDiagram X a e) (arTimeCoordinate τ) := gappedDiagram_gappedObjectVertex _ _

/-- 概要：θ の全単体を object S 値の実際の単体的射に束ねる。
方針：入力図式と Ar の時刻座標の前合成の自然性。
規約：全ての面・退化で厳密に自然。使われ方：左 fiber への持ち上げ。 -/
def mcCarthyThetaObjectMap (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    cofiberSubobjectLeftFiber X a ⊗ Δ[1] ⟶ objectSConstruction (cofiberDiagrams X.carrier) where
  app n := ↾fun p => mcCarthyThetaObjectVertex X a p.1 p.2
  naturality {n l} σ := by
    rcases n with ⟨⟨n⟩⟩
    rcases l with ⟨⟨l⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨e, τ⟩
    apply gappedDiagram_injective
    change gappedDiagram (mcCarthyThetaObjectVertex X a
      ((cofiberSubobjectLeftFiber X a).map σ e) ((Δ[1] : SSet.{u}).map σ τ)) =
        gappedDiagram ((objectSConstruction (cofiberDiagrams X.carrier)).map σ
          (mcCarthyThetaObjectVertex X a e τ))
    rw [mcCarthyThetaObjectVertex_diagram, gappedDiagram_objectS_map,
      mcCarthyThetaObjectVertex_diagram, variableTimeImage_pre, arTimeCoordinate_naturality]
    have hd := mcCarthyThetaDiagram_map X a e σ.unop
    change mcCarthyThetaDiagram X a ((cofiberSubobjectLeftFiber X a).map σ e) =
      arNerveMap σ.unop.toOrderHom ≫ mcCarthyThetaDiagram X a e at hd
    rw [hd]

end SerrePositivity.KST.SConstruction
