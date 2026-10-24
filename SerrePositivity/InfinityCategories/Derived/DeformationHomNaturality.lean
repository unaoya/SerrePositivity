module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomGeneral
public import SerrePositivity.InfinityCategories.Derived.DeformationFunctorDescentHom
public import SerrePositivity.InfinityCategories.Derived.FunctorHomotopyInputExchange
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoWhiskerCancellation
/-!
概要：正規化した同じ変形円柱の類の自然性と後合成への整合性を証明する。
方針：元の円柱の交換則へ端点等式と恒等前合成の同じ射を代入する。
規約：頂点成分だけに弱めない。使われ方：K-flat 合成比較の二経路の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
/-- 恒等前合成は元の指定関手同型の順方向射を保つ。 -/
lemma functorIso_precomp_id_hom {X Y : SSet.{u}} {f g : X ⟶ Y} (e : FunctorIso f g) :
    (e.precomp (𝟙 X)).hom = e.hom := by
  have hf : SSet.mapHomotopyCategory ((pre (𝟙 X)).app Y) =
      𝟭 (SSet.HomotopyCategory ((ihom X).obj Y)) := by
    change (hoFunctor.map ((pre (𝟙 X)).app Y)).toFunctor = _
    rw [pre_id, NatTrans.id_app, CategoryTheory.Functor.map_id]
    rfl
  exact eq_of_heq (functorMapHom_heq_of_functor_eq hf e.hom)
/-- 正規化した同じ変形円柱の類は任意の指定全関手同型に自然。 -/
lemma deformationFunctorDescentHomotopy_naturality {X D Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y]
    (L : X ⟶ D) (I : D ⟶ X) (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    {T₀ T₁ : X ⟶ Y} (e : FunctorIso T₀ T₁) :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (deformationFunctorDescentHomotopy L I H T₀)) ≫ e.hom =
    ((e.precomp I).precomp L).hom ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (deformationFunctorDescentHomotopy L I H T₁)) := by
  have he : HEq ((e.precomp I).precomp L).hom (e.precomp (L ≫ I)).hom := by
    exact heq_of_eq (congrArg Iso.hom (F2.functorIso_precomp_precomp e I L))
  have hL := functorHom_comp_heq
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp H T₀))) (e.precomp (𝟙 X)).hom
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (deformationFunctorDescentHomotopy L I H T₀))) e.hom
    (Category.assoc L I T₀) (Category.id_comp T₀) (Category.id_comp T₁)
    (functorHomotopyHom_heq_of_raw_eq _ _ rfl) (heq_of_eq (functorIso_precomp_id_hom e))
  have hR := functorHom_comp_heq (e.precomp (L ≫ I)).hom
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp H T₁))) ((e.precomp I).precomp L).hom
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (deformationFunctorDescentHomotopy L I H T₁)))
    (Category.assoc L I T₀) (Category.assoc L I T₁) (Category.id_comp T₁) he.symm
    (functorHomotopyHom_heq_of_raw_eq _ _ rfl)
  exact eq_of_heq (hL.symm.trans
    ((heq_of_eq (homotopy_postcomp_iso_exchange H e)).trans hR))
/-- 同じ正規化変形円柱の後続像は、後続関手をまとめた同じ円柱の類。 -/
lemma deformationFunctorDescentHomotopy_postcomp_hom_heq {X D Y Z : SSet.{u}}
    (L : X ⟶ D) (I : D ⟶ X) (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    (T : X ⟶ Y) (Q : Y ⟶ Z) :
    HEq (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp (deformationFunctorDescentHomotopy L I H T) Q)))
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (deformationFunctorDescentHomotopy L I H (T ≫ Q)))) := by
  exact functorHomotopyHom_heq_of_raw_eq _ _ (Category.assoc _ _ _)
end SerrePositivity.InfinityCategories
