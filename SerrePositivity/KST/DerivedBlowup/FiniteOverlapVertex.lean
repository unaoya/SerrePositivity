module

public import SerrePositivity.KST.DerivedBlowup.DiagramModuleCoefficientCategory

/-!
概要：KST §3.1 の全 diagram-module 係数 dg 圏への各有限重なりの局所模型の埋め込み。
方針：一対象をその有限重なりの添字へ送り、Hom を反射的包含の標準同定で送る。
規約：全て共通基底環上の dg 圏。局所係数環への通常加群の比較とは別。
使われ方：各有限重なりへの図式加群の導来評価。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：非空有限重なりの選択 pivot による共通基底環上の局所 dg 模型。
方針：既存の有限重なりの基底制限された Koszul 模型を使う。
規約：KST §3.1。使われ方：局所への評価の行先の係数 dg 圏。 -/
abbrev FiniteOverlapVertexObject (a : I → R) (T : FiniteOverlapIndex I) :=
  FiniteOverlapBaseKoszulObject R a (finiteOverlapIndexPivot T) T.val

set_option maxHeartbeats 2000000 in
-- 局所化環の dg 構造と係数圏の反射的 Hom の積を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環の複体と共通基底環への制限の構造を照合するために必要。
/-- 概要：局所 dg 模型から全 diagram-module の係数圏への dg 埋め込み。
方針：反射的包含による Hom 同定を使い、合成公式と図式関手の恒等律で積を確認する。
規約：KST Def3.1・Lemma3.6。使われ方：局所への dg 加群制限。 -/
def finiteOverlapVertexDGFunctor (a : I → R) (T : FiniteOverlapIndex I) :
    DGFunctor R (FiniteOverlapVertexObject R a T) (BlowupDiagramCoefficientObject R a) where
  obj _ := ⟨T⟩
  map _ _ := diagramModuleHomInclusion (finiteOverlapDGAlgebraDiagram R a) (le_refl T)
  map_id _ := rfl
  map_comp x y z := by
    let F := finiteOverlapDGAlgebraDiagram R a
    change MonObj.mul (X := (F.obj T).X) ≫ diagramModuleHomInclusion F (le_refl T) =
      (diagramModuleHomInclusion F (le_refl T) ⊗ₘ diagramModuleHomInclusion F (le_refl T)) ≫
        diagramModuleComp F T T T
    have hc := diagramModuleComp_on_le F (le_refl T) (le_refl T)
    rw [show F.map (homOfLE (le_refl T)) = 𝟙 (F.obj T) from
      CategoryTheory.Functor.map_id F T] at hc
    simpa only [Mon.id_hom', id_tensorHom_id, Category.id_comp] using hc.symm

set_option maxHeartbeats 1000000 in
-- 局所化環の Hom と係数圏の反射的 Hom の同定に必要。
/-- 概要：局所模型の埋め込みは各 Hom の複体上で同型。
方針：Hom 写像は包含による複体同定射である。
規約：KST §3.1。使われ方：局所 dg 係数の全忠実な保持。 -/
theorem finiteOverlapVertexDGFunctor_map_isIso (a : I → R) (T : FiniteOverlapIndex I) (x y) :
    IsIso ((finiteOverlapVertexDGFunctor R a T).map x y) := by
  change IsIso (diagramModuleHomInclusion (finiteOverlapDGAlgebraDiagram R a) (le_refl T))
  unfold diagramModuleHomInclusion
  infer_instance

end SerrePositivity.KST.DerivedBlowup
