module

public import SerrePositivity.InfinityCategories.Sheaves.SheafCondition
public import Mathlib.CategoryTheory.Sites.Sieves.Functoriality

/-!
概要：site 同値に沿う篩の元の圏の比較を、実際の射を保つ通常関手として作る。
方針：Over.post の同値を、引き戻した篩の充満部分圏へ制限する。
  文献対応：HTT 6.2.2.6、Kerodon §7.1（Tag 02K2）の site 再添字の篩錐比較。
規約：篩の対象と全射を保持し、層条件そのものを仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- 引き戻した篩の射を、元の site 関手で送る比較。 -/
def sieveSiteFunctor (F : C ⥤ D) {U : C} (S : Sieve (F.obj U)) :
    sieveCategory (S.functorPullback F) ⥤ sieveCategory S :=
  ObjectProperty.lift (fun A : Over (F.obj U) ↦ S.arrows A.hom)
    (ObjectProperty.ι _ ⋙ Over.post F) (fun A ↦ A.property)

/-- site 関手の忠実性は篩の比較へ制限できる。 -/
instance sieveSiteFunctor_faithful (F : C ⥤ D) [F.Faithful] {U : C}
    (S : Sieve (F.obj U)) : (sieveSiteFunctor F S).Faithful where
  map_injective {A B} f g h := by
    apply ObjectProperty.hom_ext
    apply (Over.post (X := U) F).map_injective
    exact congrArg (fun t ↦ t.hom) h

/-- site 関手の充満忠実性は篩の比較へ制限できる。 -/
instance sieveSiteFunctor_full (F : C ⥤ D) [F.Faithful] [F.Full] {U : C}
    (S : Sieve (F.obj U)) : (sieveSiteFunctor F S).Full where
  map_surjective {A B} f := by
    obtain ⟨g, hg⟩ := (Over.post (X := U) F).map_surjective f.hom
    exact ⟨ObjectProperty.homMk g, by apply ObjectProperty.hom_ext; exact hg⟩

/-- 同値の先の篩の全対象は、引き戻した篩の対象から来る。 -/
instance sieveSiteFunctor_essSurj (F : C ⥤ D) [F.IsEquivalence] {U : C}
    (S : Sieve (F.obj U)) : (sieveSiteFunctor F S).EssSurj where
  mem_essImage b := by
    obtain ⟨A, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (F := Over.post (X := U) F) b.obj
    have hA : (S.functorPullback F).arrows A.hom := by
      change S.arrows ((Over.post (X := U) F).obj A).hom
      rw [← Over.w i.hom]
      exact S.downward_closed b.property i.hom.left
    exact ⟨⟨A, hA⟩, ⟨ObjectProperty.isoMk _ i⟩⟩

/-- site 同値は同じ篩の元の圏の実際の同値を与える。 -/
def sieveSiteEquivalence (e : C ≌ D) {U : C} (S : Sieve (e.functor.obj U)) :
    sieveCategory (S.functorPullback e.functor) ≌ sieveCategory S := by
  letI : (sieveSiteFunctor e.functor S).IsEquivalence := {}
  exact (sieveSiteFunctor e.functor S).asEquivalence

/-- 比較関手は元の site への図式を厳密に保つ。 -/
lemma sieveSiteFunctor_diagram (F : C ⥤ D) {U : C} (S : Sieve (F.obj U)) :
    (sieveSiteFunctor F S).op ⋙ sieveDiagram S =
      sieveDiagram (S.functorPullback F) ⋙ F.op := rfl

end SerrePositivity.InfinityCategories.Sheaves
