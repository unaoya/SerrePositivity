module

public import SerrePositivity.KST.DerivedBlowup.RepresentableUnitMap
public import SerrePositivity.KST.DerivedBlowup.DiagramModuleUnitAction
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraVertex
public import SerrePositivity.DifferentialGraded.Module.Restriction
public import SerrePositivity.DifferentialGraded.Functor.Opposite

/-!
概要：KST §3.1 の共変 representable の包含先での局所 regular 加群比較。
方針：指定包含単位から局所 Yoneda 拡張を構成し、その成分を計算する。
規約：元の係数図式と全次数の dg 加群作用を保持する。
使われ方：補助始点の representable による構造加群の局所 perfect 性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R))

/-- 概要：共変 representable Hom(i,−) を頂点 j の一対象正規表示へ制限する。
方針：局所埋め込みの二重 opposite に沿う raw dg 加群制限を使う。
規約：KST §3.1。使われ方：局所 regular 加群比較の行先。 -/
def diagramRepresentableLocalRaw (i j : J) : RightModule R (AlgebraVertex (F.obj j))ᵒᵖ :=
  restrictModule R (AlgebraVertex (F.obj j))ᵒᵖ (DiagramModuleCoefficientObject F)ᵒᵖ
    (diagramAlgebraVertexEmbedding F j).op.op (representable R (op ⟨i⟩))

/-- 概要：包含先での局所 regular 代表加群から制限 representable への指定射。
方針：包含単位を局所加群の閉零の元として Yoneda 拡張する。
規約：KST §3.1。使われ方：構造加群の局所比較を作る基本射。 -/
def diagramRepresentableLocalRegularMap {i j : J} (h : i ≤ j) :
    ForgetEnrichment.of (Complex R) (representable R (op (.point : AlgebraVertex (F.obj j)))) ⟶
      ForgetEnrichment.of (Complex R) (diagramRepresentableLocalRaw F i j) :=
  representableUnitMap R (op .point) (diagramRepresentableLocalRaw F i j)
    (diagramModuleTransitionUnit F h)

set_option maxHeartbeats 2000000 in
-- 二重 opposite の局所制限と representable の斉次作用を照合するために必要。
/-- 概要：指定局所 regular 比較の成分は Hom 複体の標準同定射。
方針：Yoneda 拡張の作用公式、opposite の符号、包含単位の作用公式を合わせる。
規約：KST §3.1。使われ方：局所比較の可逆性・擬同型性。 -/
theorem diagramRepresentableLocalRegularMap_eval {i j : J} (h : i ≤ j) :
    (moduleEvaluation R (AlgebraVertex (F.obj j))ᵒᵖ (op .point)).map
      (diagramRepresentableLocalRegularMap F h) = diagramModuleHomInclusion F h := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((moduleEvaluation R (AlgebraVertex (F.obj j))ᵒᵖ (op .point)).map
    (representableUnitMap R (op .point) (diagramRepresentableLocalRaw F i j)
      (diagramModuleTransitionUnit F h))).f q) (show (F.obj j).X.X q from z) =
    (diagramModuleHomInclusion F h).f q (show (F.obj j).X.X q from z)
  rw [representableUnitMap_apply]
  change ((representableMap R (op (⟨i⟩ : DiagramModuleCoefficientObject F))
      (op (op ⟨j⟩)) (op (op ⟨j⟩))).f q
      ((diagramModuleHomInclusion F (le_refl j)).f q z)).v 0 q (zero_add q)
      (cycleFromUnit (diagramModuleHom F i j) (diagramModuleTransitionUnit F h)).val = _
  rw [representableMap_apply, opposite_forward]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  exact diagramModuleTransitionUnit_forward F h q z

end SerrePositivity.KST.DerivedBlowup
