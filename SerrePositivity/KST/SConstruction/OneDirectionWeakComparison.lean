module
public import SerrePositivity.KST.SConstruction.OneDirectionReducedComparison
public import SerrePositivity.KST.SConstruction.CoordinateZeroBoundary
public import SerrePositivity.KST.SConstruction.ReductionPointedComparison

/-! # 一次方向の境界商の比較の弱同値性
概要：残りの全零境界は弱可縮であり、境界商上の S₁ 比較は Kan 置換後に全基点 π_* 同型。
方針：各零方向の各段の可縮性から合併へ移し、商と元の比較の局所化可逆性を使う。
規約：商や対角の Kan 性は不要。使われ方：反復間の構造射の源の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：一次方向を固定しても、残りの非空の零方向の各交差は各段で可縮 Kan。
方針：零に固定した方向を先頭の次へずらして反復 core の零方向の可縮性を使う。
規約：外側の次数は 1 のまま。使われ方：源の境界の弱可縮性。 -/
lemma oneDirection_coordinateZeroContractible (r : ℕ) (X : StableModel.{u}) :
    CoordinateZeroContractible (oneDirectionIndex r ⋙ multiCoreSConstruction (r + 1) X) := by
  intro s hs d
  obtain ⟨j, hj⟩ := hs
  apply multiCoreSConstruction_isContractibleKan_of_zero_coordinate (r + 1) X
    ((oneDirectionIndex r).obj ((zeroDirectionsIndex s).obj (fun _ => d))) j.succ
  change (Opposite.unop ((zeroCoordinateFunctor j (decide (j ∈ s))).obj (fun _ => d))).len = 0
  have hb : decide (j ∈ s) = true := by simp [hj]
  rw [hb]
  rfl

/-- 概要：一次方向の残りの全零境界は一般の座標境界の有限合併。
方針：有限上限を iSup に書き直して定義を比較する。
規約：r=0 も含む厳密等号。使われ方：一般の弱可縮性の適用。 -/
lemma oneDirectionFatBoundary_eq_coordinate (r : ℕ) (X : StableModel.{u}) :
    oneDirectionFatBoundary r X = coordinateZeroBoundary Finset.univ ∅
      (oneDirectionIndex r ⋙ multiCoreSConstruction (r + 1) X) := by
  simp only [oneDirectionFatBoundary, coordinateZeroBoundary, Finset.sup_eq_iSup,
    Finset.mem_univ, iSup_pos, Finset.insert_empty]
  rfl

/-- 概要：正の残りの反復の全零境界は局所化で一点と同値。
方針：各交差の各段の可縮性と有限合併の一般定理を使う。
規約：境界自身の Kan 性を要求しない。使われ方：源の境界商への射影の比較。 -/
lemma oneDirectionFatBoundary_toPoint_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (toUnit (oneDirectionFatBoundary (r + 1) X : SSet.{u}))) := by
  rw [oneDirectionFatBoundary_eq_coordinate]
  exact coordinateZeroBoundary_toPoint_localized_isIso Finset.univ ∅
    ⟨0, Finset.mem_univ _⟩ _ (oneDirection_coordinateZeroContractible (r + 1) X)

/-- 概要：一次方向の残りの境界を潰す射影は全 anodyne 反転関手で可逆。
方針：単射の cofiber と境界の弱可縮性を使う。
規約：実現の Kan 性は不要。使われ方：境界商上の比較の弱同値性。 -/
lemma oneDirectionReductionQuotient_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L) (r : ℕ) (X : StableModel.{u}) :
    IsIso (L.map (oneDirectionReductionQuotient r X)) :=
  cofiberQuotient_image_isIso_of_localized_toPoint L hL (oneDirectionFatBoundary (r + 1) X).ι
    (oneDirectionFatBoundary_toPoint_localized_isIso r X)

/-- 概要：境界商上の S₁ 比較は局所化で可逆。
方針：両側の商写像と元の S₁ 比較の可逆性を射影の可換式で合わせる。
規約：商の点つき射の底の射についての主張。使われ方：Kan 置換後の π_* 比較。 -/
lemma oneDirectionReducedComparison_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (oneDirectionReducedComparison r X).right) := by
  let Q := AnodyneHomotopy.anodyneQ
  have : IsIso (Q.map (oneDirectionReductionQuotient r X)) :=
    oneDirectionReductionQuotient_image_isIso Q (Localization.inverts Q anodyneExtensions) r X
  have : IsIso (Q.map (oneDirectionRealizationComparison (r + 1) X)) :=
    oneDirectionRealizationComparison_localized_isIso (r + 1) X
  have : IsIso (Q.map (boundaryReductionQuotient r X)) :=
    boundaryReductionQuotient_image_isIso Q (Localization.inverts Q anodyneExtensions) r X
  have hh : IsIso (Q.map (oneDirectionReductionQuotient r X) ≫
      Q.map (oneDirectionReducedComparison r X).right) := by
    rw [← Q.map_comp, oneDirectionReducedComparison_quotient, Q.map_comp]
    infer_instance
  exact (isIso_comp_left_iff _ _).1 hh

/-- 概要：境界商上の S₁ 比較は Kan 置換後に全基点 π_* 同型。
方針：局所化可逆性を L9 の実際のホモトピー群の比較に移す。
規約：全次数・零次数を含む。使われ方：構造射の源の Kan 模型の同値比較。 -/
lemma oneDirectionReducedComparison_kan_piIsomorphism (r : ℕ) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (Spectra.PointedKanReplacement.map (oneDirectionReducedComparison r X)).right := by
  apply pointedKanReplacement_map_piIsomorphism_of_localized_isIso
  exact oneDirectionReducedComparison_localized_isIso r X

/-- 概要：残りの境界を潰した一次方向の実現の点つき Kan 置換の関手。
方針：既存の L9 の点つき置換と合成する。
規約：入力の全 cofiber 保存射について自然。使われ方：構造射の源の Kan 模型。 -/
def oneDirectionKanRealizationFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u} :=
  oneDirectionReducedRealizationFunctor r ⋙ Spectra.PointedKanReplacement.functor

/-- 概要：一次方向の境界商の置換は Kan。
方針：L9 の置換の Kan 性。
規約：全ての反復に適用。使われ方：π_* と Ω の比較。 -/
instance oneDirectionKanRealization_kanComplex (r : ℕ) (X : StableModel.{u}) :
    KanComplex (((oneDirectionKanRealizationFunctor r).obj X).right) :=
  Spectra.PointedKanReplacement.obj_kanComplex _

/-- 概要：境界商上の一次方向の比較を Kan 置換した自然変換。
方針：比較の自然変換に点つき Kan 置換を後合成する。
規約：全成分が π_* 同型。使われ方：構造射の源の自然な同値比較。 -/
def oneDirectionKanComparisonNat (r : ℕ) :
    oneDirectionKanRealizationFunctor r ⟶ boundaryKanRealizationFunctor r :=
  Functor.whiskerRight (oneDirectionReducedComparisonNat r) Spectra.PointedKanReplacement.functor

local instance (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right := Spectra.loopSpace_kanComplex Y

/-- 概要：一次方向の境界商の比較に Ω を適用する。
方針：点つき Kan 置換した比較を円からの点つき内部 Hom で写す。
規約：delooping の Ω 条件とは別の模型比較。使われ方：loop 模型の自然な比較。 -/
def oneDirectionLoopComparisonNat (r : ℕ) :
    oneDirectionKanRealizationFunctor r ⋙
      PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u} ⟶
    boundaryKanRealizationFunctor r ⋙
      PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u} :=
  Functor.whiskerRight (oneDirectionKanComparisonNat r)
    (PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u})

local instance (r : ℕ) (X : StableModel.{u}) :
    KanComplex (((oneDirectionKanRealizationFunctor r ⋙
      PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u}).obj X).right) :=
  Spectra.loopSpace_kanComplex _

local instance (r : ℕ) (X : StableModel.{u}) :
    KanComplex (((boundaryKanRealizationFunctor r ⋙
      PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u}).obj X).right) :=
  Spectra.loopSpace_kanComplex _

/-- 概要：境界商上の一次方向の比較は Ω 後も全基点 π_* 同型。
方針：Kan な点つき対象間の π_* 同型を L9 の写像空間へ移す。
規約：全次数・零次数を含む。使われ方：反復の loop 模型の比較。 -/
lemma oneDirectionLoopComparison_piIsomorphism (r : ℕ) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((oneDirectionLoopComparisonNat r).app X).right :=
  Spectra.PointedMapping.post_piIsomorphism PointedSimplicialSet.circle
    (Spectra.PointedKanReplacement.map (oneDirectionReducedComparison r X))
    (oneDirectionReducedComparison_kan_piIsomorphism r X)

end SerrePositivity.KST.SConstruction
