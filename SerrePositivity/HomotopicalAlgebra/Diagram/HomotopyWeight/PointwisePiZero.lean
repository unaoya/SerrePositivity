module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.PointwiseTensorFrame

/-!
# 始域 frame の重み付き錐と図式の局所化 Hom

概要：Hovey §5.4 の重み付き錐の連結成分で図式の導来 Hom を計算する。
方針：実際の図式 frame の Hom 同型・π₀ 比較・零次同型を合成する。
規約：元の置換図式を始域とし、単体集合のモデル構造は仮定しない。
使われ方：定値図式を始域とする一般 homotopy 極限の Hom 比較。
-/

@[expose] public section

noncomputable section

universe u v w t

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex

variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{0, u} C]
  [ModelCategory C] [ModelCategory (K ⥤ C)]
  (W : K ⥤ SSet.{u}) (B : SimplexCategory ⥤ C)
  (hW : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries K).rlp.llp (initial.to W))
  (hB : reedyLeft simplex (cofibrations C) (initial.to B))
  (htriv : ∀ {F G : K ⥤ C} (p : F ⟶ G), trivialFibrations (K ⥤ C) p →
    ∀ k, trivialFibrations C (p.app k))
  (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
  (hfib : ∀ {F G : K ⥤ C} (p : F ⟶ G), Fibration p → ∀ k, Fibration (p.app k))
  {D : Type w} [Category.{t} D] (Q : (K ⥤ C) ⥤ D)
  [Q.IsLocalization (weakEquivalences (K ⥤ C))]

/-- 概要：重み付き始域 Hom の π₀ は置換図式からの局所化 Hom（Hovey §5.4）。
方針：構成した図式 frame の通常の π₀ 比較を Hom 同型と零次同型で移す。
規約：終域図式は fibrant、始域は元の各値の重み実現。
使われ方：定値図式からの導来 Hom を重み付き錐で表示する。 -/
def pointwiseWeightedHomPiZeroEquiv (F : K ⥤ C) [IsFibrant F] :
    SSet.π₀ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHom K W B).obj F) ≃
      (Q.obj ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseRealization K B).obj W) ⟶ Q.obj F) := by
  have hc := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrame_reedyCofibrant K W B hW hB htriv
  have := cosimplicialFrame_isCofibrant_obj (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrame K W B) hc (SimplexCategory.mk 0)
  exact ((SSet.π₀Functor.mapIso ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameHomIso K W B).app F).symm).toEquiv).trans
    ((piZeroLocalizationEquiv (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrame K W B)
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrame_homotopicallyConstant K W B hW hB hconst hfib) Q hc F).trans
      (Iso.homCongr (Q.mapIso (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameZeroIso K W B)) (Iso.refl _)))

/-- 概要：零単体の比較は同じ図式射の局所化（Hovey §5.4）。
方針：Hom 同型の逆を相殺し、図式 frame の零次の計算を使う。
規約：零次同型の逆だけを前置する。
使われ方：図式の射に関する π₀ 比較の自然性。 -/
lemma pointwiseWeightedHomPiZeroEquiv_mk {F : K ⥤ C} [IsFibrant F]
    (f : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrame K W B).obj (SimplexCategory.mk 0) ⟶ F) :
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHomPiZeroEquiv K W B hW hB htriv hconst hfib Q F
      (SSet.mapπ₀ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameHomIso K W B).app F).hom (SSet.π₀.mk f)) =
      Q.map (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameZeroIso K W B).inv ≫ Q.map f := by
  have := cosimplicialFrame_isCofibrant_obj (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrame K W B)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrame_reedyCofibrant K W B hW hB htriv) (SimplexCategory.mk 0)
  change Q.map (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameZeroIso K W B).inv ≫
    piZeroLocalizationEquiv (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrame K W B)
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrame_homotopicallyConstant K W B hW hB hconst hfib) Q
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrame_reedyCofibrant K W B hW hB htriv) F
      (SSet.mapπ₀ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameHomIso K W B).app F).inv
        (SSet.mapπ₀ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameHomIso K W B).app F).hom (SSet.π₀.mk f))) ≫ 𝟙 _ = _
  rw [← SSet.mapπ₀_comp_apply, Iso.hom_inv_id, SSet.mapπ₀_id_apply,
    piZeroLocalizationEquiv_mk, Category.comp_id]

/-- 概要：重み付き始域 Hom の π₀ 比較は終域図式の射に自然（Hovey §5.4）。
方針：零単体の表示と実際の Hom 同型の自然性を使う。
規約：後合成は元の図式射の局所化。
使われ方：定値図式からの導来 Hom の自然同値。 -/
lemma pointwiseWeightedHomPiZeroEquiv_target {F G : K ⥤ C} [IsFibrant F] [IsFibrant G]
    (g : F ⟶ G) (z : SSet.π₀ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHom K W B).obj F)) :
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHomPiZeroEquiv K W B hW hB htriv hconst hfib Q G
      (SSet.mapπ₀ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHom K W B).map g) z) =
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHomPiZeroEquiv K W B hW hB htriv hconst hfib Q F z ≫ Q.map g := by
  let e := (SSet.π₀Functor.mapIso ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameHomIso K W B).app F)).toEquiv
  obtain ⟨z, rfl⟩ := e.surjective z
  induction z using SSet.π₀.rec with | mk f =>
  change _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHomPiZeroEquiv K W B hW hB htriv hconst hfib Q G
      (SSet.mapπ₀ _ (SSet.mapπ₀ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameHomIso K W B).app F).hom (SSet.π₀.mk f))) =
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHomPiZeroEquiv K W B hW hB htriv hconst hfib Q F
      (SSet.mapπ₀ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameHomIso K W B).app F).hom (SSet.π₀.mk f)) ≫ Q.map g
  have hn : ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameHomIso K W B).app F).hom ≫
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHom K W B).map g =
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrame K W B)).map g ≫
      ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameHomIso K W B).app G).hom :=
    ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameHomIso K W B).hom.naturality g).symm
  rw [← SSet.mapπ₀_comp_apply, hn, SSet.mapπ₀_comp_apply, SSet.mapπ₀_mk,
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHomPiZeroEquiv_mk, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHomPiZeroEquiv_mk]
  change Q.map (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameZeroIso K W B).inv ≫ Q.map (f ≫ g) = _
  rw [Q.map_comp, Category.assoc]

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
