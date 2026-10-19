module
public import SerrePositivity.InfinityCategories.Derived.DGModuleCycleFaithful
public import SerrePositivity.InfinityCategories.DGNerve.HomotopyCategory

/-! # dg 加群の実ホモトピー逆から nerve の同値辺へ

概要：両合成の全 Hom end の原始元から実際の nerve の辺の可逆性を得る。
方針：閉加群射の商の同型を構成し、検証済みの dg nerve の h 比較で同型を反映する。
規約：ホモトピー逆と両原始元を入力する。使われ方：β3 の fiber/cofiber 比較辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 閉加群射の実辺を元の閉射へ戻すと元に等しい。 -/
lemma dgModuleEdge_closed (f : M ⟶ N) :
    edgeClosed (dgModuleEdge A D f).toTruncated = f :=
  (edgeClosedEquiv (Simplex.vertex (ForgetEnrichment.to (Complex A) M))
    (Simplex.vertex (ForgetEnrichment.to (Complex A) N))).apply_symm_apply f

/-- 両合成の実原始元から加群のホモトピー商の同型を構成する。 -/
def dgModuleHomotopyIsoOfInverse (f : M ⟶ N) (g : N ⟶ M)
    (hfg : ModuleHomotopy A D (f ≫ g) (𝟙 M))
    (hgf : ModuleHomotopy A D (g ≫ f) (𝟙 N)) :
    (moduleToHomotopy A D).obj M ≅ (moduleToHomotopy A D).obj N where
  hom := (moduleToHomotopy A D).map f
  inv := (moduleToHomotopy A D).map g
  hom_inv_id := by
    rw [← CategoryTheory.Functor.map_comp]
    exact ((moduleToHomotopy_map_eq_iff A D _ _).2 ⟨hfg⟩).trans
      ((moduleToHomotopy A D).map_id M)
  inv_hom_id := by
    rw [← CategoryTheory.Functor.map_comp]
    exact ((moduleToHomotopy_map_eq_iff A D _ _).2 ⟨hgf⟩).trans
      ((moduleToHomotopy A D).map_id N)

/-- ホモトピー商で可逆な閉加群射の実 nerve 辺の類は同型。 -/
lemma dgModuleEdge_isIso_of_homotopy (f : M ⟶ N)
    (hf : IsIso ((moduleToHomotopy A D).map f)) :
    IsIso (SSet.Truncated.HomotopyCategory₂.homMk (dgModuleEdge A D f).toTruncated) := by
  let F := toH0 A (RightModule A D)
  have hi : IsIso (F.map
      (SSet.Truncated.HomotopyCategory₂.homMk (dgModuleEdge A D f).toTruncated)) := by
    change IsIso ((toH0 A (RightModule A D)).map
      (SSet.Truncated.HomotopyCategory₂.homMk (dgModuleEdge A D f).toTruncated))
    rw [toH0_homMk, dgModuleEdge_closed]
    exact hf
  exact isIso_of_reflects_iso _ F

/-- 指定した逆射と両原始元から実辺の可逆性を得る。 -/
lemma dgModuleEdge_isIso_of_inverse (f : M ⟶ N) (g : N ⟶ M)
    (hfg : ModuleHomotopy A D (f ≫ g) (𝟙 M))
    (hgf : ModuleHomotopy A D (g ≫ f) (𝟙 N)) :
    IsIso (SSet.Truncated.HomotopyCategory₂.homMk (dgModuleEdge A D f).toTruncated) := by
  apply dgModuleEdge_isIso_of_homotopy A D
  change IsIso (dgModuleHomotopyIsoOfInverse A D f g hfg hgf).hom
  infer_instance

end SerrePositivity.InfinityCategories
