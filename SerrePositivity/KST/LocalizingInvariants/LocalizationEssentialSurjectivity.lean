module

public import SerrePositivity.KST.LocalizingInvariants.LocalizationUniqueness

/-!
概要：全関手 ∞ 圏の局所化普遍性を持つ射は、元の頂点の像で本質的に全射である。
方針：本質像の全部分 quasicategory への因子化を下ろし、前合成の充満忠実性で戻す。
規約：特定の貼合せ模型には依存しない。使われ方：商の全ての辺の元の分数表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def localizationEssentialImage {X Q : SSet.{u}} (F : X ⟶ Q) : Set (Q _⦋0⦌) :=
  {q | ∃ x : X _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (F.app (Opposite.op ⦋0⦌) x) q)}

def localizationImageSubcomplex {X Q : SSet.{u}} (F : X ⟶ Q) : Q.Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Q (localizationEssentialImage F)

def localizationImageLift {X Q : SSet.{u}} (F : X ⟶ Q) :
    X ⟶ (localizationImageSubcomplex F : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (localizationEssentialImage F) F (fun x => ⟨x, ⟨Iso.refl _⟩⟩)

lemma localizationImageLift_ι {X Q : SSet.{u}} (F : X ⟶ Q) :
    localizationImageLift F ≫ (localizationImageSubcomplex F).ι = F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

lemma localizationImageLift_inverts {X Q : SSet.{u}} [Quasicategory Q]
    (F : X ⟶ Q) (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (localizationImageLift F) W := by
  intro s hs
  have : Quasicategory (localizationImageSubcomplex F : SSet.{u}) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι Q
    (localizationEssentialImage F)).reflects_isInvertibleEdge
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s).map ((truncation 2).map F))
    (f := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s).map ((truncation 2).map (localizationImageLift F))).map
      ((truncation 2).map (localizationImageSubcomplex F).ι)) rfl).mp (hF hs)

lemma localization_isEssentiallySurjective {X Q : SSet.{u}} [Quasicategory Q]
    (F : X ⟶ Q) (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective F := by
  have : Quasicategory (localizationImageSubcomplex F : SSet.{u}) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _
  let K := localizationDescend F W hF (localizationImageLift F)
    (localizationImageLift_inverts F W hF.choose)
  let e := localizationDescendIso F W hF (localizationImageLift F)
    (localizationImageLift_inverts F W hF.choose)
  have d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ (K ≫ (localizationImageSubcomplex F).ι)) (F ≫ 𝟙 Q) := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e (localizationImageSubcomplex F).ι
    rw [localizationImageLift_ι] at h
    simpa only [Category.assoc, Category.comp_id] using h
  let c := localizationFactorizationIso F W hF d
  intro q
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (K.app (Opposite.op ⦋0⦌) q)
  obtain ⟨x, ⟨a⟩⟩ := h
  exact ⟨x, ⟨a ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app c q⟩⟩

end SerrePositivity.KST.LocalizingInvariants
