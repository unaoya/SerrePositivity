module

public import SerrePositivity.InfinityCategories.Sheaves.RelativeCechDiagram
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetCoconeAugmentationCriterion

/-!
概要：元の相対 Čech 増大の点の comma は、同じ slice の Hom 値図式の要素圏。
方針：同じ次数と同じ射を使い、点を保つ条件を Over の可換条件へ読み替える。
規約：HTT 4.1.3.1 の comma の収縮への表示の法則。頂点や増大を取り替えない。
使われ方：S8 の各評価で選んだ根を、構成済みの収縮へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [Category.{v} C] {P Q V : C}
variable (f : P ⟶ Q) [HasFiniteProducts (Over Q)] (r : V ⟶ Q)

/-- 元の増大の点 r の comma。 -/
abbrev RelativeCechPointComma :=
  CostructuredArrow (elementsCoconeFunctor (relativeCechHomCocone f V)) (Discrete.mk r)

/-- 点を保つ同じ射を、slice の Hom の元として読む。 -/
def relativeCechPointCommaToElements : RelativeCechPointComma f r ⥤
    (cechPointDiagram (relativeCechData f) (Over.mk r)).Elements where
  obj a := (cechPointDiagram (relativeCechData f) (Over.mk r)).elementsMk a.left.obj
    (Over.homMk a.left.val (Discrete.eq_of_hom a.hom))
  map g := Functor.Elements.homMk g.left.hom (by
    apply Over.OverMorphism.ext
    exact g.left.map_val)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- slice の同じ射を、元の増大の同じ点への対象へ戻す。 -/
def relativeCechPointCommaFromElements :
    (cechPointDiagram (relativeCechData f) (Over.mk r)).Elements ⥤
      RelativeCechPointComma f r where
  obj a := CostructuredArrow.mk
    (Y := ((AsSmall.down ⋙ (relativeCechData f).obj ⋙ Over.forget Q ⋙
      coyoneda.obj (Opposite.op V)).elementsMk a.obj a.val.left))
    (eqToHom (Discrete.ext (Over.w a.val)))
  map g := CostructuredArrow.homMk (Functor.Elements.homMk g.hom (by
    exact congrArg CommaMorphism.left g.map_val)) (Subsingleton.elim _ _)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 元の増大の点の comma と同じ slice の Hom の表示は、順逆の同じ作用素を持つ。 -/
def relativeCechPointCommaEquivalence : RelativeCechPointComma f r ≌
    (cechPointDiagram (relativeCechData f) (Over.mk r)).Elements :=
  CategoryTheory.Equivalence.mk (relativeCechPointCommaToElements f r)
    (relativeCechPointCommaFromElements f r)
    (NatIso.ofComponents (fun a => CostructuredArrow.isoMk (Iso.refl _) (Subsingleton.elim _ _))
      (by
        intro a b g
        apply CostructuredArrow.hom_ext
        apply Functor.Elements.Hom.ext
        rfl)) (eqToIso (by rfl))

/-- 各評価で与えた根一本は、元の増大の同じ点の comma を収縮させる。 -/
lemma relativeCechPointComma_isWeaklyContractible (a : V ⟶ P) (ha : a ≫ f = r) :
    IsWeaklyContractible (CategoryTheory.nerve (RelativeCechPointComma f r)) := by
  exact (nerveQCatEquivalence (relativeCechPointCommaEquivalence f r)).isQCatEquivalence
    |>.isWeakHomotopyEquivalence.weaklyContractible_iff.mpr
      (cechPointElements_isWeaklyContractible (relativeCechData f) (Over.homMk a ha))

/-- 各 Hom の射が持ち上がれば、同じ Hom 値 Čech 余錐は空間の余極限余錐。 -/
lemma relativeCechHomCocone_isColimit
    (hlift : ∀ r : V ⟶ Q, ∃ a : V ⟶ P, a ≫ f = r) :
    IsColimitCone (strictNativeCocone (setsToKan.mapCocone (relativeCechHomCocone f V))) := by
  apply strictSetCocone_isColimit_of_contractible_comma
  rintro ⟨r⟩
  obtain ⟨a, ha⟩ := hlift r
  exact relativeCechPointComma_isWeaklyContractible f r a ha

end SerrePositivity.InfinityCategories.Sheaves
