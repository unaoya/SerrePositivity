module

public import SerrePositivity.DifferentialGraded.Module.Yoneda
public import SerrePositivity.DifferentialGraded.Module.ClosedMaps

/-!
概要：KST §3.1 の局所 regular 加群比較に使う閉零 Yoneda 拡張。
方針：単位複体から値への射を全次数 Yoneda 自然変換へ拡張する。
規約：通常圏の射にも全次数自然性を保持する。
使われ方：指定包含単位から representable と局所構造加群を比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open DifferentialGraded CochainComplex HomComplex

variable (R : Type u) [CommRing R] {D : Type v} [DGCategory R D] [Small.{u} D]

/-- 概要：指定閉零の元から代表加群の閉零射を構成する。
方針：単位パラメータ Yoneda 拡張を通常 chain map 族として主 Hom へ送る。
規約：KST §3.1。使われ方：局所 regular 加群比較の指定射。 -/
def representableUnitMap (x : D) (M : RightModule R D)
    (ψ : 𝟙_ (Complex R) ⟶ M.obj (op x)) :
    ForgetEnrichment.of (Complex R) (representable R x) ⟶
      ForgetEnrichment.of (Complex R) M :=
  moduleMorphismMk R D (closedTransApp R (yonedaExtension R x M ψ))
    (closedTransApp_naturality R (yonedaExtension R x M ψ))

/-- 概要：指定 Yoneda 射の成分は元の Yoneda 拡張を閉零射として読んだもの。
方針：主 Hom への構成の評価公式を使う。
規約：KST §3.1。使われ方：局所比較の具体的な成分計算。 -/
theorem representableUnitMap_eval (x : D) (M : RightModule R D)
    (ψ : 𝟙_ (Complex R) ⟶ M.obj (op x)) (y : D) :
    (moduleEvaluation R D y).map (representableUnitMap R x M ψ) =
      mapFromUnit R _ _ (yonedaExtensionApp R x M ψ (op y)) :=
  moduleMorphismMk_eval R D _ _ y

/-- 概要：指定閉零 Yoneda 射は元の閉零の元への加群作用として計算される。
方針：閉零射の cochain を単位複体の生成元で評価し、全次数 Yoneda の公式を使う。
規約：KST §3.1。使われ方：単位元の作用による局所比較の可逆性の計算。 -/
theorem representableUnitMap_apply (x : D) (M : RightModule R D)
    (ψ : 𝟙_ (Complex R) ⟶ M.obj (op x)) (y : D) (q : ℤ) (h : GradedHom R y x q) :
    (((moduleEvaluation R D y).map (representableUnitMap R x M ψ)).f q) h =
      moduleAction R M (x := op x) (y := op y) h
        (cycleFromUnit (M.obj (op x)) ψ).val (zero_add q) := by
  rw [representableUnitMap_eval]
  change (Cochain.ofHom (mapFromUnit R _ _ (yonedaExtensionApp R x M ψ (op y)))).v
    q q (add_zero q) h = _
  rw [mapFromUnit_cochain]
  change ((yonedaExtensionApp R x M ψ (op y)).f 0 _).v q q (add_zero q) h = _
  rw [yonedaExtensionApp_apply]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  rfl

end SerrePositivity.KST.DerivedBlowup
