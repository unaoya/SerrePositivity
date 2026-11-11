module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservingFunctorSpaces
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LeftAdjointAllColimitPreservation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatSimplicial
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Quasicategory

/-!
概要：Pr^L・Pr^R の保存条件付き全関手圏を単体的豊穣圏にまとめる。
方針：全部分関手圏の合成を持ち上げ、core へ豊穣構造を移送して coherent nerve を取る。
規約：左側は小余極限保存、右側は accessible な小極限保存を使い、随伴存在判定に依存しない。
使われ方：Pr^L・Pr^R の全 ∞ 圏の定義と双対性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：左・右の保存条件を同じ全関手に課す。
方針：true は小余極限、false は accessibility と小極限を選ぶ。
規約：二条件の同値を仮定しない。
使われ方：二つの豊穣圏の共通の構成。 -/
def PresentableFunctorCondition (left : Bool) {C D : SSet.{u + 1}} (F : C ⟶ D) : Prop :=
  if left then _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits F else _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor F ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits F

lemma presentableFunctorCondition_id (left : Bool) (C : SSet.{u + 1}) [Quasicategory C] :
    PresentableFunctorCondition left (𝟙 C) := by
  cases left
  · exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isAccessibleFunctor_id C, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.adjunction_preservesSmallLimits (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.refl C)⟩
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.adjunction_preservesSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.refl C)

lemma PresentableFunctorCondition.comp {left : Bool} {C D E : SSet.{u + 1}}
    {F : C ⟶ D} {G : D ⟶ E}
    (hF : PresentableFunctorCondition left F) (hG : PresentableFunctorCondition left G) :
    PresentableFunctorCondition left (F ≫ G) := by
  cases left
  · exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor.comp hF.1 hG.1, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservesSmallLimits.comp hF.2 hG.2⟩
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservesSmallColimits.comp hF hG

/-- 概要：保存する方向で区別した presentable 圏の対象型。
方針：共通の束縛対象を型同義として使う。
規約：方向は対象の性質を変更しない。
使われ方：二つの豊穣構造の instance を区別する。 -/
def PresentableEnrichedObjects (_left : Bool) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}

def preservingFunctorPredicate (left : Bool) (C D : PresentableEnrichedObjects.{u} left)
    (v : ((ihom C.obj).obj D.obj) _⦋0⦌) : Prop :=
  PresentableFunctorCondition left ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C.obj D.obj).symm v)

def preservingFunctorHom (left : Bool) (C D : PresentableEnrichedObjects.{u} left) :
    SSet.{u + 1} := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (preservingFunctorPredicate left C D)

instance preservingFunctorHom_quasicategory (left : Bool)
    (C D : PresentableEnrichedObjects.{u} left) :
    Quasicategory (preservingFunctorHom left C D) := by
  dsimp [preservingFunctorHom]
  infer_instance

def preservingFunctorId (left : Bool) (C : PresentableEnrichedObjects.{u} left) :
    𝟙_ SSet.{u + 1} ⟶ preservingFunctorHom left C C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (MonoidalClosed.id C.obj) (by
    intro a
    have : Subsingleton ((𝟙_ SSet.{u + 1}) _⦋0⦌) :=
      inferInstanceAs (Subsingleton PUnit.{u + 2})
    have ha : a = SSet.unitHomEquiv (𝟙_ SSet.{u + 1}) (𝟙 _) := Subsingleton.elim _ _
    rw [ha]
    change PresentableFunctorCondition left (𝟙 C.obj)
    exact presentableFunctorCondition_id left C.obj)

def preservingFunctorComp (left : Bool) (C D E : PresentableEnrichedObjects.{u} left) :
    preservingFunctorHom left C D ⊗ preservingFunctorHom left D E ⟶
      preservingFunctorHom left C E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (preservingFunctorPredicate left C D)).ι ⊗ₘ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (preservingFunctorPredicate left D E)).ι) ≫
        MonoidalClosed.comp C.obj D.obj E.obj) (by
    rintro ⟨f, g⟩
    obtain ⟨F, hF⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C.obj D.obj).surjective f.val
    obtain ⟨G, hG⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv D.obj E.obj).surjective g.val
    have hf : PresentableFunctorCondition left F := by
      simpa only [preservingFunctorPredicate, ← hF, Equiv.symm_apply_apply] using
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex f
    have hg : PresentableFunctorCondition left G := by
      simpa only [preservingFunctorPredicate, ← hG, Equiv.symm_apply_apply] using
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex g
    change PresentableFunctorCondition left ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C.obj E.obj).symm
      ((MonoidalClosed.comp C.obj D.obj E.obj).app _ (f.val, g.val)))
    rw [← hF, ← hG]
    change PresentableFunctorCondition left ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C.obj E.obj).symm
      ((MonoidalClosed.comp C.obj D.obj E.obj).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)))
    have he : (MonoidalClosed.comp C.obj D.obj E.obj).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ G) := by rfl
    rw [he]
    change PresentableFunctorCondition left ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C.obj E.obj).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C.obj E.obj) (F ≫ G)))
    rw [Equiv.symm_apply_apply]
    exact PresentableFunctorCondition.comp hf hg)

lemma preservingFunctor_id_comp (left : Bool) (C D : PresentableEnrichedObjects.{u} left) :
    (λ_ (preservingFunctorHom left C D)).inv ≫ preservingFunctorId left C ▷ _ ≫
      preservingFunctorComp left C C D = 𝟙 _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  apply Subtype.ext
  change (MonoidalClosed.comp C.obj C.obj D.obj).app n
    ((MonoidalClosed.id C.obj).app n PUnit.unit, f.val) = f.val
  exact congrArg (fun q : (ihom C.obj).obj D.obj ⟶ (ihom C.obj).obj D.obj ↦
    q.app n f.val) (MonoidalClosed.id_comp C.obj D.obj)

lemma preservingFunctor_comp_id (left : Bool) (C D : PresentableEnrichedObjects.{u} left) :
    (ρ_ (preservingFunctorHom left C D)).inv ≫ _ ◁ preservingFunctorId left D ≫
      preservingFunctorComp left C D D = 𝟙 _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  apply Subtype.ext
  change (MonoidalClosed.comp C.obj D.obj D.obj).app n
    (f.val, (MonoidalClosed.id D.obj).app n PUnit.unit) = f.val
  exact congrArg (fun q : (ihom C.obj).obj D.obj ⟶ (ihom C.obj).obj D.obj ↦
    q.app n f.val) (MonoidalClosed.comp_id C.obj D.obj)

lemma preservingFunctor_assoc (left : Bool) (B C D E : PresentableEnrichedObjects.{u} left) :
    (α_ (preservingFunctorHom left B C) (preservingFunctorHom left C D)
      (preservingFunctorHom left D E)).inv ≫
        preservingFunctorComp left B C D ▷ preservingFunctorHom left D E ≫
      preservingFunctorComp left B D E =
        preservingFunctorHom left B C ◁ preservingFunctorComp left C D E ≫
          preservingFunctorComp left B C E := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨f, g, h⟩
  apply Subtype.ext
  change (MonoidalClosed.comp B.obj D.obj E.obj).app n
      ((MonoidalClosed.comp B.obj C.obj D.obj).app n (f.val, g.val), h.val) =
    (MonoidalClosed.comp B.obj C.obj E.obj).app n
      (f.val, (MonoidalClosed.comp C.obj D.obj E.obj).app n (g.val, h.val))
  exact congrArg (fun q : (ihom B.obj).obj C.obj ⊗
      ((ihom C.obj).obj D.obj ⊗ (ihom D.obj).obj E.obj) ⟶ (ihom B.obj).obj E.obj ↦
    q.app n (f.val, (g.val, h.val))) (MonoidalClosed.assoc B.obj C.obj D.obj E.obj)

instance presentableEnrichedCategory (left : Bool) :
    EnrichedCategory SSet.{u + 1} (PresentableEnrichedObjects.{u} left) where
  Hom := preservingFunctorHom left
  id := preservingFunctorId left
  comp := preservingFunctorComp left
  id_comp := preservingFunctor_id_comp left
  comp_id := preservingFunctor_comp_id left
  assoc := preservingFunctor_assoc left

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
