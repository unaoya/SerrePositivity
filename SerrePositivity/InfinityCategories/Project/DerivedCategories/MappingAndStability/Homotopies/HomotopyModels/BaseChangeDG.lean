module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.ScalarRestrictionNerve
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.SemifreeBaseChange
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.SemifreeSubcategory
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.CategoriesAndModules

/-! # 底変更の dg 関手

概要：複体の底変更は、値域の係数を制限すると dg 関手になる。
方針：係数拡大の Hom 比較を随伴の単位で転置する。
規約：平坦性は不要。使われ方：semifree dg nerve の底変更。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open DifferentialGraded.ScalarExtension
variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

private lemma transpose_id (X : Complex S) (Y : Complex T)
    (i : 𝟙_ (Complex S) ⟶ X) (j : 𝟙_ (Complex T) ⟶ Y)
    (m : (extension f).obj X ⟶ Y)
    (h : Functor.LaxMonoidal.ε (extension f) ≫ (extension f).map i ≫ m = j) :
    i ≫ (adjunction f).unit.app X ≫ (restriction f).map m =
      Functor.LaxMonoidal.ε (restriction f) ≫ (restriction f).map j := by
  have hn := (adjunction f).unit.naturality i
  simp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc]
  have hu := NatTrans.IsMonoidal.unit (τ := (adjunction f).unit)
  simp only [Functor.LaxMonoidal.id_ε, Category.id_comp, Functor.LaxMonoidal.comp_ε] at hu
  rw [hu, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, h]

private lemma transpose_comp (K L M : Complex S) (K' L' M' : Complex T)
    (i : K ⊗ L ⟶ M) (j : K' ⊗ L' ⟶ M')
    (a : (extension f).obj K ⟶ K') (b : (extension f).obj L ⟶ L')
    (c : (extension f).obj M ⟶ M')
    (h : Functor.LaxMonoidal.μ (extension f) K L ≫ (extension f).map i ≫ c =
      (a ⊗ₘ b) ≫ j) :
    i ≫ (adjunction f).unit.app M ≫ (restriction f).map c =
      (((adjunction f).unit.app K ≫ (restriction f).map a) ⊗ₘ
        ((adjunction f).unit.app L ≫ (restriction f).map b)) ≫
        Functor.LaxMonoidal.μ (restriction f) K' L' ≫ (restriction f).map j := by
  have hn := (adjunction f).unit.naturality i
  simp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc]
  have ht := NatTrans.IsMonoidal.tensor (τ := (adjunction f).unit) K L
  simp only [Functor.LaxMonoidal.id_μ, Category.id_comp, Functor.LaxMonoidal.comp_μ] at ht
  rw [ht, Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, h,
    Functor.map_comp, ← tensorHom_comp_tensorHom, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_assoc]

/-- 概要：係数拡大した Hom からの dg 関手を随伴で転置する。
方針：随伴の単位の monoidal 性が単位と合成の保存を与える。
規約：対象写像は変更しない。使われ方：底変更の S 線形 dg 関手。 -/
def transposeBaseChangeDG {D : Type v} {E : Type w} [DGCategory S D] [DGCategory T E]
    (F : DGFunctor T (DGBaseChange f D) E) : DGFunctor S D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.DGRestrictScalars f E) where
  obj x := F.obj x
  map x y := (adjunction f).unit.app (homObject S D x y) ≫ (restriction f).map (F.map x y)
  map_id x := by
    apply transpose_id f
    have h := F.map_id x
    change (Functor.LaxMonoidal.ε (extension f) ≫
      (extension f).map (eId (Complex S) (C := D) x)) ≫ F.map x x = _ at h
    exact (Category.assoc _ _ _).symm.trans h
  map_comp x y z := by
    apply transpose_comp f
    have h := F.map_comp x y z
    change (Functor.LaxMonoidal.μ (extension f) _ _ ≫
      (extension f).map (eComp (Complex S) (C := D) x y z)) ≫ F.map x z = _ at h
    exact (Category.assoc _ _ _).symm.trans h

/-- 概要：複体の底変更を S 線形 dg 関手として与える。
方針：全次数 Hom の係数拡大比較を随伴で転置する。
規約：対象は T ⊗_S P。使われ方：semifree 部分圏への制限。 -/
def complexBaseChangeDG : DGFunctor S (Complex S) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.DGRestrictScalars f (Complex T)) :=
  transposeBaseChangeDG f (complexDGFunctor f)

/-- 概要：semifree 複体の底変更は S 線形 dg 関手である。
方針：複体の dg 関手を充満部分圏に制限し、既存の semifree 保存定理を添える。
規約：値域は T 上の semifree dg 圏の係数制限。使われ方：D(S) の底変更。 -/
def semifreeBaseChangeDG : DGFunctor S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.DGRestrictScalars f (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree T)) where
  obj P := ⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f).obj P.val, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_baseChange f P.property⟩
  map P Q := (complexBaseChangeDG f).map P.val Q.val
  map_id P := (complexBaseChangeDG f).map_id P.val
  map_comp P Q R := (complexBaseChangeDG f).map_comp P.val Q.val R.val

end SerrePositivity.InfinityCategories.Project.DerivedCategories
