module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.StandardSimplexCosimplicialHom
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.AdjunctionHom
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.KanTensorAdjunction

/-!
概要：積・内部 Hom の随伴で、cf 置換を含む frame Hom と豊穣 Hom を照合する。
方針：標準単体の tensor frame、結合子、通常の随伴の各次数の Hom 同型を合成する。
規約：SSet の全対象は cofibrant。両対象の anodyne Kan 置換を実際に用いる。
使われ方：HTT 4.2.4.1・5.2.4.6、γ4 の具体的な入力検証。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.HomotopyFunctionComplex
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 単体集合の標準 tensor frame。 -/
abbrev kanTensorFrame (X : SSet.{u}) : SimplexCategory ⥤ SSet.{u} :=
  SSet.stdSimplex ⋙ tensorLeft X

/-- frame Hom と実際の内部 Hom の、終域に自然な同型。 -/
def kanTensorFrameHomIso (X : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (kanTensorFrame X) ≅ ihom X :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.adjunctionHomIsoSameUniverse (ihom.adjunction X) SSet.stdSimplex ≪≫
    Functor.isoWhiskerLeft _ QuillenStandardFrame.homIso ≪≫ Functor.rightUnitor _

/-- tensor frame の左像と tensor の左像の frame を比較する実際の結合子。 -/
def kanTensorFrameAssocIso (K X : SSet.{u}) :
    kanTensorFrame (K ⊗ X) ≅ kanTensorFrame X ⋙ tensorLeft K :=
  NatIso.ofComponents (fun n ↦ α_ K X (SSet.stdSimplex.obj n)) (by
    intro n m f
    exact associator_naturality_right K X (SSet.stdSimplex.map f))

/-- 結合子の逆で前合成し、通常の随伴を frame の全次数に適用する。 -/
def kanTensorFrameAdjunctionIso (K X : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (kanTensorFrame (K ⊗ X)) ≅ ihom K ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (kanTensorFrame X) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor.mapIso (kanTensorFrameAssocIso K X).symm.op ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.adjunctionHomIsoSameUniverse (ihom.adjunction K) (kanTensorFrame X)

/-- 内部 curry の任意のパラメータでの公式。零単体だけの比較ではない。 -/
lemma kanIhomCurry_parameter {K X Y T : SSet.{u}} (f : (K ⊗ X) ⊗ T ⟶ Y) :
    curry f ≫ ihomCurry K X Y = curry (curry ((α_ K X T).inv ≫ f)) := by
  apply uncurry_injective
  apply uncurry_injective
  simp only [uncurry_natural_left, uncurry_uncurry_ihomCurry, uncurry_curry]
  rw [associator_inv_naturality_right_assoc, ← uncurry_eq, uncurry_curry]

/-- frame の各次数の通常の Hom 随伴同型は、豊穣 Hom 同型と厳密に可換。 -/
lemma kanTensorFrameAdjunction_square (K X Y : SSet.{u}) :
    ((kanTensorFrameAdjunctionIso K X).app Y).hom ≫
        ((kanTensorFrameHomIso X).app ((ihom K).obj Y)).hom =
      ((kanTensorFrameHomIso (K ⊗ X)).app Y).hom ≫ ihomCurry K X Y := by
  ext n f
  change SSet.yonedaEquiv (curry (curry ((α_ K X (SSet.stdSimplex.obj n.unop)).inv ≫ f))) =
    (ihomCurry K X Y).app n (SSet.yonedaEquiv (curry f))
  rw [← SSet.yonedaEquiv_comp, kanIhomCurry_parameter]

/-- 固定した Quillen cofibration 類（単射）を積は保つ。 -/
lemma kanTensor_preserves_cofibration (K : SSet.{u}) {X Y : SSet.{u}} (f : X ⟶ Y)
    [Cofibration f] : Cofibration (K ◁ f) := by
  have : Mono (K ◁ f) := by
    constructor
    intro Z a b h
    apply CartesianMonoidalCategory.hom_ext
    · simpa using congrArg (fun g ↦ g ≫ CartesianMonoidalCategory.fst K Y) h
    · apply (cancel_mono f).mp
      simpa only [Category.assoc, CartesianMonoidalCategory.whiskerLeft_snd] using
        congrArg (fun g ↦ g ≫ CartesianMonoidalCategory.snd K Y) h
  exact cofibration_of_mono _

/-- 固定した trivial cofibration 類（anodyne 射）を積は保つ。 -/
lemma kanTensor_preserves_anodyne (K : SSet.{u}) {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : anodyneExtensions f) : anodyneExtensions (K ◁ f) :=
  hf.whiskerLeft K

/-- 固定した Quillen fibration 類を内部 Hom は保つ。 -/
lemma kanInternalHom_preserves_fibration (K : SSet.{u}) {X Y : SSet.{u}} (f : X ⟶ Y)
    [Fibration f] : Fibration ((ihom K).map f) := inferInstance

/-- 内部 Hom は trivial Kan fibration も保つ。全境界に対する随伴を使う。 -/
lemma kanInternalHom_preserves_trivialKanFibration (K : SSet.{u})
    {X Y : SSet.{u}} (p : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((ihom K).map p) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).mpr
  intro n
  have : Cofibration (boundary n).ι := cofibration_of_mono _
  have := kanTensor_preserves_cofibration K (boundary n).ι
  exact ((ihom.adjunction K).hasLiftingProperty_iff (boundary n).ι p).mp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) (K ◁ (boundary n).ι) inferInstance)

/-- K × X → K × RX は anodyne。K が Kan なら終域は上で構成した cf 左像。 -/
lemma kanTensorReplacement_leftComparison_anodyne (K X : SSet.{u}) :
    anodyneExtensions (K ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit X) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit_anodyne X).whiskerLeft K

/-- 置換後も全対象が cofibrant。別の cofibrant 置換の選択は不要。 -/
lemma kanTensorReplacement_isCofibrant (X : SSet.{u}) : IsCofibrant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject X).obj :=
  ⟨(cofibration_iff _).mp (cofibration_of_mono _)⟩

/-- 置換した対象は fibrant（全ホーンを充填）。 -/
lemma kanTensorReplacement_isFibrant (X : SSet.{u}) : IsFibrant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject X).obj :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject X).isKanComplex

/-- 積の左像の cf 性。K と X は Kan で、cofibrancy は自動。 -/
lemma kanTensorReplacement_left_isFibrant (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (X : SSet.{u}) :
    IsFibrant ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject X)).obj :=
  ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject X)).isKanComplex

/-- 実際の cf 置換を代入した frame Hom の随伴同型。 -/
def kanReplacedTensorFrameAdjunctionIso (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (X Y : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (kanTensorFrame (K.obj ⊗ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject X).obj))).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject Y).obj ≅
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (kanTensorFrame (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject X).obj)).obj
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanInternalHom K.obj).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject Y)).obj :=
  (kanTensorFrameAdjunctionIso K.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject X).obj).app (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject Y).obj

/-- cf 置換を含む frame と豊穣 Hom の比較。単体的 Hom 同型の具体的な入力を照合する。 -/
lemma kanReplacedTensorFrameAdjunction_square (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (X Y : SSet.{u}) :
    (kanReplacedTensorFrameAdjunctionIso K X Y).hom ≫
        ((kanTensorFrameHomIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject X).obj).app
          ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanInternalHom K.obj).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject Y)).obj).hom =
      ((kanTensorFrameHomIso (K.obj ⊗ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject X).obj)).app
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject Y).obj).hom ≫
          (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorAdjunctionHomIso K).val (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject X)).app
            (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject Y)).hom :=
  kanTensorFrameAdjunction_square K.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject X).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject Y).obj

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
