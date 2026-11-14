module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedParameterCylinderCategory

/-!
概要：パラメータ付き豊穣自然変換から円柱上の実際の豊穣関手を作る。
方針：端をまたぐ Hom は評価と後合成で送り、自然性を合成保存に使う。
規約：元の自然変換の全パラメータを保持する。使われ方：Sp の評価の coherent な族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.EnrichedParameterCylinder
end SerrePositivity.KST.Spectra.EnrichedParameterCylinder
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder
variable {C : Type v} {D : Type w} [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]
  (A : SSet.{u}) (F G : EnrichedFunctor SSet.{u} C D)
  (η : GradedNatTrans (Center.ofBraidedObj A) F G)

/-- 空な Hom からの一意な射。 -/
def emptyTo (Y : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.empty ⟶ Y where
  app _ := ↾fun e ↦ e.elim
  naturality {d e} f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact x.elim

/-- 円柱の両端には元の二つの関手の対象を置く。 -/
def functorObject (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) : D :=
  match X.side with
  | false => F.obj X.val
  | true => G.obj X.val

/-- 端をまたぐ射を、指定したパラメータ付き自然変換で送る。 -/
def functorMap : (X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) →
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.hom A X Y ⟶ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorObject A F G X ⟶[SSet] _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorObject A F G Y)
  | ⟨false, x⟩, ⟨false, y⟩ => F.map x y
  | ⟨false, x⟩, ⟨true, y⟩ => (η.app x ⊗ₘ G.map x y) ≫ eComp SSet (F.obj x) (G.obj x) (G.obj y)
  | ⟨true, _⟩, ⟨false, _⟩ => _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.emptyTo _
  | ⟨true, x⟩, ⟨true, y⟩ => G.map x y

/-- 円柱の恒等射は元の関手の恒等射へ送られる。 -/
lemma functorMap_id (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.identity A X ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorMap A F G η X X = eId SSet (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorObject A F G X) := by
  rcases X with ⟨s, x⟩
  cases s
  · exact F.map_id x
  · exact G.map_id x

/-- 元の自然性を任意の単体パラメータで評価した式。 -/
lemma naturality_app (X Y : C) (d : SimplexCategoryᵒᵖ) (a : A.obj d)
    (f : (X ⟶[SSet] Y).obj d) :
    (eComp SSet (F.obj X) (F.obj Y) (G.obj Y)).app d
        ((F.map X Y).app d f, (η.app Y).app d a) =
      (eComp SSet (F.obj X) (G.obj X) (G.obj Y)).app d
        ((η.app X).app d a, (G.map X Y).app d f) := by
  let af : (A ⊗ (X ⟶[SSet] Y)).obj d := (a, f)
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (η.naturality X Y) d) af
  exact h

/-- 豊穣関手の合成保存を二つの単体で評価する。 -/
lemma functor_comp_app (H : EnrichedFunctor SSet.{u} C D) (X Y Z : C)
    (d : SimplexCategoryᵒᵖ) (a : (X ⟶[SSet] Y).obj d) (b : (Y ⟶[SSet] Z).obj d) :
    (H.map X Z).app d ((eComp SSet X Y Z).app d (a, b)) =
      (eComp SSet (H.obj X) (H.obj Y) (H.obj Z)).app d
        ((H.map X Y).app d a, (H.map Y Z).app d b) := by
  let ab : ((X ⟶[SSet] Y) ⊗ (Y ⟶[SSet] Z)).obj d := (a, b)
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (H.map_comp X Y Z) d) ab
  exact h

/-- 円柱の合成は、自然性と元の関手の合成保存で保たれる。 -/
lemma functorMap_comp (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.composition A X Y Z ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorMap A F G η X Z =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorMap A F G η X Y ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorMap A F G η Y Z) ≫
        eComp SSet (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorObject A F G X) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorObject A F G Y)
          (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorObject A F G Z) := by
  rcases X with ⟨s, x⟩
  rcases Y with ⟨t, y⟩
  rcases Z with ⟨r, z⟩
  cases s <;> cases t <;> cases r
  all_goals
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨a, b⟩
  · exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functor_comp_app F x y z d a b
  · rcases b with ⟨p, b⟩
    have hg := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functor_comp_app G x y z d a b
    change (eComp SSet (F.obj x) (G.obj x) (G.obj z)).app d
      ((η.app x).app d p, (G.map x z).app d ((eComp SSet x y z).app d (a, b))) = _
    rw [hg, ← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_assoc_app]
    rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.naturality_app A F G η x y d p a]
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_assoc_app (F.obj x) (F.obj y) (G.obj y) (G.obj z) d
      ((F.map x y).app d a) ((η.app y).app d p) ((G.map y z).app d b)
  · exact b.elim
  · rcases a with ⟨p, a⟩
    have hg := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functor_comp_app G x y z d a b
    change (eComp SSet (F.obj x) (G.obj x) (G.obj z)).app d
      ((η.app x).app d p, (G.map x z).app d ((eComp SSet x y z).app d (a, b))) = _
    rw [hg]
    exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_assoc_app (F.obj x) (G.obj x) (G.obj y) (G.obj z) d
      ((η.app x).app d p) ((G.map x y).app d a) ((G.map y z).app d b)).symm
  · exact a.elim
  · exact a.elim
  · exact b.elim
  · exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functor_comp_app G x y z d a b

/-- 元のパラメータ付き豊穣自然変換が定める実際の円柱の関手。 -/
def evaluationFunctor : EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) D where
  obj := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorObject A F G
  map := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorMap A F G η
  map_id := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorMap_id A F G η
  map_comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorMap_comp A F G η

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.emptyTo (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.emptyTo := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.emptyTo

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.evaluationFunctor (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.evaluationFunctor := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.evaluationFunctor

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.functorMap := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.functorMap_comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorMap_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.functorMap_id := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorMap_id

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorObject (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.functorObject := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorObject

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.functor_comp_app := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functor_comp_app

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.naturality_app := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.naturality_app

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.emptyTo._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.emptyTo._proof_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorMap.match_1 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.functorMap.match_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorMap.match_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorObject.match_1 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.functorObject.match_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functorObject.match_1
