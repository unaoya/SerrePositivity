module

public import SerrePositivity.KST.Spectra.RestrictionSourceSquare
public import SerrePositivity.KST.Spectra.SkeletalRelativeRepresentatives
public import SerrePositivity.KST.Spectra.CellMappingCoordinates

/-!
概要：骨格の制限 fiber を一つのセルの境界制限 fiber へ写す実際の射。
方針：セル付着の正方形を制限の正方形へ移し、商射で球面包含との一致を検査する。
規約：通常のセル球面とその向きを保持する。
使われ方：Goerss–Jardine VIII §1。塔の微分のセルごとの連結射への帰着。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

instance skeletalInclusion_mono (K : SSet.{u}) (n : ℕ) :
    Mono (UnbasedPointedMapping.skeletalInclusion K n) := by
  dsimp only [UnbasedPointedMapping.skeletalInclusion]
  infer_instance

def cellBoundarySource (K : SSet.{u}) (d : ℕ)
    (c : relativeCellComplexOfMono.Cell (K.skeleton d).ι d) :
    (boundary d : SSet.{u}) ⟶ (K.skeleton d : SSet.{u}) :=
  c.ιSigmaBoundary ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.attachingMap K d

def cellSimplexSource (K : SSet.{u}) (d : ℕ)
    (c : relativeCellComplexOfMono.Cell (K.skeleton d).ι d) :
    (Δ[d] : SSet.{u}) ⟶ (K.skeleton (d + 1) : SSet.{u}) :=
  c.ιSigmaStdSimplex ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.characteristicMap K d

lemma cellSourceSquare (K : SSet.{u}) (d : ℕ)
    (c : relativeCellComplexOfMono.Cell (K.skeleton d).ι d) :
    cellBoundarySource K d c ≫
        Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ d)) =
      (boundary d).ι ≫ cellSimplexSource K d c := by
  have h := congrArg (fun f ↦ c.ιSigmaBoundary ≫ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.isPushout K d).w
  simpa only [cellBoundarySource, cellSimplexSource, relativeCellComplexOfMono.l,
    Sigma.ι_map_assoc, Category.assoc] using h

/-- 概要：セルの源の正方形から誘導される相対商の射は既存の球面包含。
方針：球面の商写像への前合成で両辺を検査する。
規約：相対商の比較同型の逆射を用いる向き。
使われ方：Goerss–Jardine VIII §1。連結射のセル制限と係数表示の接続。 -/
lemma cellSourceMap_eq_inclusion (K : SSet.{u}) (d : ℕ)
    (c : relativeCellComplexOfMono.Cell (K.skeleton d).ι d) :
    UnbasedPointedMapping.relativeSourceMap
        (Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ d))) (boundary d).ι
        (cellBoundarySource K d c) (cellSimplexSource K d c) (cellSourceSquare K d c) =
      cellSphereInclusion K d c ≫ (relativeCofiberIso K d).inv := by
  apply pointedCofiber_hom_ext (PointedObject.adjoinFunctor.map (boundary.{u} d).ι)
  rw [UnbasedPointedMapping.relativeSourceMap_projection]
  have h := cellRestriction_projection K
    (UnbasedPointedMapping.relativeSource
      (Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ d)))) d (𝟙 _) c
  simpa only [cellSimplexSource, Functor.map_comp, Category.assoc, cellRestriction,
    cellSphereInclusion, Category.comp_id] using h.symm

/-- 概要：実際の骨格 fiber を指定セルの境界制限の fiber へ写す。
方針：セルの源の正方形が誘導する制限 fiber の射を使う。
規約：Kan 性はこの定義には不要。
使われ方：Goerss–Jardine VIII §1。塔の微分をセル境界で計算する射。 -/
def cellBoundaryFiberMap (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) (n : ℕ)
    (c : relativeCellComplexOfMono.Cell (K.skeleton (n + 1)).ι (n + 1)) :
    UnbasedPointedMapping.stageFiber K Y n ⟶
      pointedFiber (UnbasedPointedMapping.pre (boundary (n + 1)).ι Y) :=
  UnbasedPointedMapping.restrictionSourceFiberMap
    (UnbasedPointedMapping.skeletalInclusion K n) (boundary (n + 1)).ι
    (cellBoundarySource K (n + 1) c) (cellSimplexSource K (n + 1) c)
    (cellSourceSquare K (n + 1) c) Y

/-- 概要：セル境界 fiber への実際の制限は既存のセル球面の制限と可換。
方針：相対商の源の自然性とセル球面包含の式を合成する。
規約：fiber の射そのものの厳密な可換式。
使われ方：Goerss–Jardine VIII §1。係数と連結準同型の同じセルでの比較。 -/
@[reassoc]
lemma stageFiberCellIso_boundaryFiber (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) (n : ℕ)
    (c : relativeCellComplexOfMono.Cell (K.skeleton (n + 1)).ι (n + 1)) :
    (stageFiberCellIso K Y n).hom ≫ cellBoundaryFiberMap K Y n c =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (cellSphereInclusion K (n + 1) c) Y ≫
        (UnbasedPointedMapping.restrictionFiberIso (boundary (n + 1)).ι Y).hom := by
  change (((MonoidalClosed.pre (relativeCofiberIso K (n + 1)).hom).app Y) ≫
    (UnbasedPointedMapping.stageFiberIso K Y n).hom) ≫ _ = _
  rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, Category.assoc]
  change _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (relativeCofiberIso K (n + 1)).hom Y ≫
    ((UnbasedPointedMapping.restrictionFiberIso _ Y).hom ≫
      UnbasedPointedMapping.restrictionSourceFiberMap _ _ _ _ _ Y) = _
  rw [← UnbasedPointedMapping.restrictionFiberIso_source, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp, cellSourceMap_eq_inclusion,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[reassoc]
lemma cellBoundaryFiberMap_sphere (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) (n : ℕ)
    (c : relativeCellComplexOfMono.Cell (K.skeleton (n + 1)).ι (n + 1)) :
    cellBoundaryFiberMap K Y n c ≫
        (UnbasedPointedMapping.restrictionFiberIso (boundary (n + 1)).ι Y).inv =
      (stageFiberCellIso K Y n).inv ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (cellSphereInclusion K (n + 1) c) Y := by
  have h := congrArg (fun t ↦ (stageFiberCellIso K Y n).inv ≫ t ≫
      (UnbasedPointedMapping.restrictionFiberIso (boundary (n + 1)).ι Y).inv)
    (stageFiberCellIso_boundaryFiber K Y n c)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using h

/-- 概要：実際のセル境界 fiber への制限で既存の正次数の係数を計算できる。
方針：球面への制限をセル境界 fiber と相対商の同型の合成に置き換える。
規約：各セルの向きと正次数の係数同型は既存のものを使用する。
使われ方：Goerss–Jardine VIII §1。連結準同型の自然性による微分の局所計算。 -/
lemma stageFiberCoefficientEquiv_boundaryRestriction (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n r : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y n).right r
      (UnbasedPointedMapping.stageFiber K Y n).basepoint) (s : K.nonDegenerate (n + 1)) :
    stageFiberCoefficientEquiv K Y n r x s = SimplexCell.positiveHomotopyEquiv Y n r
      (pointedGroupMap r
        (UnbasedPointedMapping.restrictionFiberIso (boundary (n + 1)).ι Y).inv
        (pointedGroupMap r (cellBoundaryFiberMap K Y n ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).symm s)) x)) := by
  rw [stageFiberCoefficientEquiv_restriction, ← pointedGroupMap_comp,
    ← cellBoundaryFiberMap_sphere, pointedGroupMap_comp]
  rfl

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
