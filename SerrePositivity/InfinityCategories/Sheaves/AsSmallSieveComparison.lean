module

public import SerrePositivity.InfinityCategories.Sheaves.NativeSiteDescent
public import SerrePositivity.InfinityCategories.Sheaves.SiteSmallModelShape

/-!
概要：小さい site を AsSmall に表示したとき、元の引き戻し篩の圏を比較する。
方針：Over.post の同値を既存の充満部分圏に制限し、AsSmall の同値を合成する。
使われ方：HTT 6.2.2.6、Kerodon §7.1（Tag 02K2）の site の同値による輸送。
規約：係数の宇宙は変えず、被覆篩の全射を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {U : C}

/-- AsSmall に表示した篩への、元の引き戻し篩の全射を保つ比較関手。 -/
def asSmallSieveFunctor (S : Sieve ((AsSmall.up : C ⥤ AsSmall.{u + 1} C).obj U)) :
    AsSmall.{u + 1} (sieveCategory (S.functorPullback AsSmall.up)) ⥤ sieveCategory S :=
  ObjectProperty.lift (fun A : Over (AsSmall.up.obj U) ↦ S.arrows A.hom)
    (AsSmall.down ⋙ ObjectProperty.ι _ ⋙ Over.post AsSmall.up)
    (fun A ↦ (AsSmall.down.obj A).property)

/-- 包みの移送と充満包含は、篩の比較の忠実性を保つ。 -/
instance asSmallSieveFunctor_faithful
    (S : Sieve ((AsSmall.up : C ⥤ AsSmall.{u + 1} C).obj U)) :
    (asSmallSieveFunctor S).Faithful := by
  letI : (AsSmall.up : C ⥤ AsSmall.{u + 1} C).IsEquivalence :=
    (AsSmall.equiv (C := C)).isEquivalence_functor
  constructor
  intro A B f g h
  apply ULift.ext
  apply ObjectProperty.hom_ext
  apply (Over.post (X := U) (AsSmall.up : C ⥤ AsSmall.{u + 1} C)).map_injective
  exact congrArg (fun t ↦ t.hom) h

/-- 包みの移送と充満包含は、篩の比較の充満性を保つ。 -/
instance asSmallSieveFunctor_full
    (S : Sieve ((AsSmall.up : C ⥤ AsSmall.{u + 1} C).obj U)) :
    (asSmallSieveFunctor S).Full := by
  letI : (AsSmall.up : C ⥤ AsSmall.{u + 1} C).IsEquivalence :=
    (AsSmall.equiv (C := C)).isEquivalence_functor
  constructor
  intro A B f
  obtain ⟨g, hg⟩ :=
    (Over.post (X := U) (AsSmall.up : C ⥤ AsSmall.{u + 1} C)).map_surjective f.hom
  refine ⟨ULift.up (ObjectProperty.homMk g), ?_⟩
  apply ObjectProperty.hom_ext
  exact hg

/-- 元の Over 圏の同値から、すべての篩の対象を回収する。 -/
instance asSmallSieveFunctor_essSurj
    (S : Sieve ((AsSmall.up : C ⥤ AsSmall.{u + 1} C).obj U)) :
    (asSmallSieveFunctor S).EssSurj where
  mem_essImage b := by
    letI : (AsSmall.up : C ⥤ AsSmall.{u + 1} C).IsEquivalence :=
      (AsSmall.equiv (C := C)).isEquivalence_functor
    obtain ⟨A, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage
      (F := Over.post (X := U) (AsSmall.up : C ⥤ AsSmall.{u + 1} C)) b.obj
    have hA : (S.functorPullback AsSmall.up).arrows A.hom := by
      change S.arrows ((Over.post (AsSmall.up : C ⥤ AsSmall.{u + 1} C)).obj A).hom
      rw [← Over.w i.hom]
      exact S.downward_closed b.property i.hom.left
    exact ⟨AsSmall.up.obj (⟨A, hA⟩ : sieveCategory (S.functorPullback AsSmall.up)),
      ⟨ObjectProperty.isoMk _ i⟩⟩

/-- 同じ元の篩の圏を、係数と同じ宇宙の通常圏の同値で比較する。 -/
def asSmallSieveEquivalence
    (S : Sieve ((AsSmall.up : C ⥤ AsSmall.{u + 1} C).obj U)) :
    AsSmall.{u + 1} (sieveCategory (S.functorPullback AsSmall.up)) ≌ sieveCategory S := by
  letI : (asSmallSieveFunctor S).IsEquivalence := {}
  exact (asSmallSieveFunctor S).asEquivalence

/-- 包みと opposite の順序の変更も含めた、元の篩の形状の同値。 -/
def asSmallSieveShapeEquivalence
    (S : Sieve ((AsSmall.up : C ⥤ AsSmall.{u + 1} C).obj U)) :
    QCatEquivalence (presheafShape (sieveCategory (S.functorPullback AsSmall.up)))
      (nerve (sieveCategory S)ᵒᵖ) := by
  let A := sieveCategory (S.functorPullback AsSmall.up)
  let e : AsSmall.{u + 1} Aᵒᵖ ≌ (AsSmall.{u + 1} A)ᵒᵖ :=
    (AsSmall.equiv (C := Aᵒᵖ)).symm.trans (AsSmall.equiv (C := A)).op
  exact (qCatEquivalenceOfIso (nerveAsSmallIso.{u, u + 1} Aᵒᵖ)).trans
    ((nerveQCatEquivalence e).trans (nerveQCatEquivalence (asSmallSieveEquivalence S).op))

end SerrePositivity.InfinityCategories.Sheaves
