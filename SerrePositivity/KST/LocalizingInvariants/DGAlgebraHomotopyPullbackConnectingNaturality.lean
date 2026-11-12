module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackConnecting

/-!
概要：元の cospan 三成分に沿う接続射の自然性と、第一脚の接続像の零性。
方針：同じ差の cocone 三角形の射と実複体同型を用いて比較する。
規約：接続射の選択を取り替えない。使われ方：対角のホモロジー pro 核判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] {A₀ B₀ C₀ A₁ B₁ C₁ : Mon (Complex R)}
  (f₀ : A₀ ⟶ B₀) (g₀ : C₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) (g₁ : C₁ ⟶ B₁)
  (a : A₀ ⟶ A₁) (b : B₀ ⟶ B₁) (c : C₀ ⟶ C₁)
  (hf : a ≫ f₁ = f₀ ≫ b) (hg : c ≫ g₁ = g₀ ≫ b)

lemma map_fromMappingCocone :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap (difference R f₀ g₀) (difference R f₁ g₁)
      (sumMap R a c) b.hom (difference_comm R _ _ _ _ _ _ _ hf hg) ≫
      (complexIso R f₁ g₁).inv =
    (complexIso R f₀ g₀).inv ≫ (map R f₀ g₀ f₁ g₁ a b c hf hg).hom := by
  apply (cancel_mono (complexIso R f₁ g₁).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc]
  have hm : (map R f₀ g₀ f₁ g₁ a b c hf hg).hom ≫ (complexIso R f₁ g₁).hom =
      (complexIso R f₀ g₀).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap (difference R f₀ g₀)
        (difference R f₁ g₁) (sumMap R a c) b.hom (difference_comm R _ _ _ _ _ _ _ hf hg) :=
    map_toMappingCocone R _ _ _ _ _ _ _ _ _
  rw [hm, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

lemma connecting_naturality (n : ℤ) :
    homologyMap b.hom (n - 1) ≫ connecting R f₁ g₁ n =
      connecting R f₀ g₀ n ≫ homologyMap (map R f₀ g₀ f₁ g₁ a b c hf hg).hom n := by
  let φ := cochainCoconeTriangleMap (difference R f₀ g₀) (difference R f₁ g₁)
    (sumMap R a c) b.hom (difference_comm R _ _ _ _ _ _ _ hf hg)
  have hn := cochainTriangleHomologyConnecting_naturality φ (n - 1) n (by omega)
  have hh := congrArg (fun t => t ≫ homologyMap (complexIso R f₁ g₁).inv n) hn
  unfold connecting
  refine (Category.assoc _ _ _).symm.trans (hh.trans ?_)
  change (homologyδOfTriangle (mappingCocone.triangle (difference R f₀ g₀))
      (n - 1) n (by omega) ≫ homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap
        (difference R f₀ g₀) (difference R f₁ g₁) (sumMap R a c) b.hom
          (difference_comm R _ _ _ _ _ _ _ hf hg)) n) ≫ _ = _
  rw [Category.assoc, ← homologyMap_comp,
    map_fromMappingCocone, homologyMap_comp, ← Category.assoc]

variable {A B C : Mon (Complex R)} (f : A ⟶ B) (g : C ⟶ B)

lemma left_connecting_zero (n : ℤ) :
    homologyMap f.hom (n - 1) ≫ connecting R f g n = 0 := by
  have hi : (biprod.inl : A.X ⟶ A.X ⊞ C.X) ≫ difference R f g = f.hom := by
    simp only [difference, biprod.inl_desc]
  have hz := homologyMap_homologyδOfTriangle (mappingCocone.triangle (difference R f g))
    (DerivedCategory.mappingCocone_triangle_distinguished _) (n - 1) n (by omega)
  let δ : B.X.homology (n - 1) ⟶ (mappingCocone (difference R f g)).homology n :=
    homologyδOfTriangle (mappingCocone.triangle (difference R f g)) (n - 1) n (by omega)
  have hz' : homologyMap (difference R f g) (n - 1) ≫ δ = 0 := hz
  change homologyMap f.hom (n - 1) ≫ (δ ≫ homologyMap (complexIso R f g).inv n) = 0
  rw [← hi, homologyMap_comp, Category.assoc, ← Category.assoc
    (homologyMap (difference R f g) (n - 1)), hz']
  simp

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
