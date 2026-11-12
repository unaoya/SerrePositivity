module
public import SerrePositivity.KST.SConstruction.DGStrictCommaFamily

/-! # 閉比較族の実 comma Hom 作用の単位保存
概要：比較 cochain 零の実 Hom 作用が、元の二関手の恒等射を保持することを証明する。
方針：二射影と比較 cochain で射を判定し、比較の前合成を全複体で照合する。
規約：全 Hom 複体を保持。使われ方：標準 dg 対角の厳密な関手法則。
-/
@[expose] public section
noncomputable section
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]
  {E : Type w} [DGCategory R E] {F : DGFunctor R C E}

/-- 実 comma Hom の比較は、元の全パラメータの前合成と可換。 -/
lemma dgStrictCommaComparison_precompose (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
    {K L : Complex R} (a : K ⟶ L)
    (f : L ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R C E F X Y K (a ≫ f) =
      (Cochain.ofHom a).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R C E F X Y L f)
        (zero_add (-1)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex] at f ⊢
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

namespace DGStrictCommaFamily
variable {P : Type t} [DGCategory R P] (d : DGStrictCommaFamily R C E F P)

/-- 同じ実 Hom 作用は、元の二関手の単位と同じ comma 単位を厳密に保存する。 -/
lemma homMap_id (x : P) :
    eId (Complex R) x ≫ d.homMap x x =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity R C E F (d.obj x) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHom_ext R C E F (d.obj x) (d.obj x)
  · rw [Category.assoc, d.homMap_source, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_source]
    exact d.source.map_id x
  · rw [Category.assoc, d.homMap_replacement, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_replacement]
    exact d.replacement.map_id x
  · rw [dgStrictCommaComparison_precompose, d.homMap_comparison,
      Cochain.comp_zero, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_comparison]

end DGStrictCommaFamily
end SerrePositivity.KST.SConstruction
