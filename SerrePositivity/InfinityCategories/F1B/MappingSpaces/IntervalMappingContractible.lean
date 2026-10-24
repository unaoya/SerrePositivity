module

public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalMappingOpposite
public import SerrePositivity.InfinityCategories.F1B.Cofinality.InitialMappingSpace
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.RightIntervalEquivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceTerminal

/-!
概要：区間写像空間の可縮性は標的の反転で保存・検出され、始対象性を検出する。
方針：境界と標準単体で族を正規化して反転し、右 pinched 模型との比較を使う。
規約：反転による境界充填の移送には quasicategory 性を使わない。
使われ方：comma の正方形表示から始対象性へ戻る際の模型比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：境界の逆反転も包含と可換。
方針：反転同型の順方向との合成を消去する。
規約：周囲の標準単体でも逆向きに反転する。
使われ方：充填した反転族の境界を回収する。 -/
lemma boundaryReverseIso_inv_ι (n : ℕ) :
    SSet.opFunctor.map (boundary n).ι ≫ (stdSimplex.opIso ⦋n⦌).hom =
      (boundaryReverseIso.{u} n).inv ≫ (boundary n).ι := by
  apply (cancel_epi (boundaryReverseIso n).hom).mp
  rw [← Category.assoc, boundaryReverseIso_hom_ι, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- 概要：反転標的の区間写像空間が可縮なら元の区間写像空間も可縮。
方針：境界上の族を反転し、その充填を逆反転して戻す。
規約：単体集合は任意、端点は交換して反転する。
使われ方：左模型による可縮性を区間模型へ移す。 -/
lemma intervalMappingSpace_isContractibleKan_of_op {X : SSet.{u}} (x y : X _⦋0⦌)
    (h : IsContractibleKan (intervalMappingSpace (X := X.op)
      (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x))) :
    IsContractibleKan (intervalMappingSpace x y) := by
  intro n b
  let g := (boundaryReverseIso n).hom ≫ intervalReverseFamily b
  obtain ⟨F, hF⟩ := h n g
  refine ⟨intervalUnreverseFamily ((stdSimplex.opIso ⦋n⦌).hom ≫ F), ?_⟩
  rw [← intervalUnreverseFamily_precomp]
  have he : SSet.opFunctor.map (boundary n).ι ≫ ((stdSimplex.opIso ⦋n⦌).hom ≫ F) =
      intervalReverseFamily b := by
    rw [← Category.assoc, boundaryReverseIso_inv_ι, Category.assoc, hF]
    exact Iso.inv_hom_id_assoc _ _
  rw [he, intervalUnreverseFamily_reverse]

/-- 概要：元の区間写像空間が可縮なら反転標的の交換された区間写像空間も可縮。
方針：反転した境界を元へ戻して充填し、充填を再び反転する。
規約：strict な境界の等式を保つ。
使われ方：始対象判定の区間模型から反転した右模型へ移る。 -/
lemma intervalMappingSpace_op_isContractibleKan {X : SSet.{u}} (x y : X _⦋0⦌)
    (h : IsContractibleKan (intervalMappingSpace x y)) :
    IsContractibleKan (intervalMappingSpace (X := X.op)
      (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)) := by
  intro n b
  let g := intervalUnreverseFamily ((boundaryReverseIso n).inv ≫ b)
  obtain ⟨F, hF⟩ := h n g
  refine ⟨(stdSimplex.opIso ⦋n⦌).inv ≫ intervalReverseFamily F, ?_⟩
  rw [← Category.assoc, ← boundaryReverseIso_hom_ι, Category.assoc,
    ← intervalReverseFamily_precomp, hF]
  dsimp only [g]
  rw [intervalReverseFamily_unreverse, Iso.hom_inv_id_assoc]

/-- 概要：区間写像空間の可縮性は反転標的の交換された区間模型で検出できる。
方針：境界充填の移送の両方向を合わせる。
規約：元の単体集合の quasicategory 性は不要。
使われ方：始対象と終対象の区間模型による双対の判定。 -/
lemma intervalMappingSpace_op_isContractibleKan_iff {X : SSet.{u}} (x y : X _⦋0⦌) :
    IsContractibleKan (intervalMappingSpace (X := X.op)
      (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)) ↔
      IsContractibleKan (intervalMappingSpace x y) :=
  ⟨intervalMappingSpace_isContractibleKan_of_op x y,
    intervalMappingSpace_op_isContractibleKan x y⟩

/-- 概要：始対象から出る全ての区間写像空間は可縮。
方針：反転した終対象の右 pinched 模型を区間模型へ移して戻す。
規約：X は quasicategory。
使われ方：始対象条件と正方形で記述した写像空間の照合。 -/
lemma IsInitialVertex.intervalMappingSpace_isContractibleKan {X : SSet.{u}}
    [Quasicategory X] {x : X _⦋0⦌} (hx : IsInitialVertex x) (y : X _⦋0⦌) :
    IsContractibleKan (intervalMappingSpace x y) := by
  apply intervalMappingSpace_isContractibleKan_of_op x y
  exact (SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_isQCatEquivalence
    (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)).choose.isContractibleKan
      (hx.op_isTerminalVertex.pinchedHom_isContractibleKan (SSet.opObjEquiv.symm y))

/-- 概要：全ての出る区間写像空間が可縮な頂点は始対象。
方針：区間模型の反転不変性と右 pinched 比較で終対象判定へ移す。
規約：X の quasicategory 性を仮定する。
使われ方：comma の正方形の可縮性から普遍矢印性へ戻す。 -/
lemma isInitialVertex_of_intervalMappingSpace_isContractibleKan {X : SSet.{u}}
    [Quasicategory X] (x : X _⦋0⦌)
    (h : ∀ y : X _⦋0⦌, IsContractibleKan (intervalMappingSpace x y)) : IsInitialVertex x := by
  apply isInitialVertex_of_isTerminalVertex_op
  apply isTerminalVertex_of_pinchedHom_isContractibleKan
  intro z
  apply (SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_isQCatEquivalence z
    (SSet.opObjEquiv.symm x)).choose.isContractibleKan_iff.mpr
  exact intervalMappingSpace_op_isContractibleKan x (SSet.opObjEquiv z) (h _)

/-- 概要：始対象性は全ての出る区間写像空間の可縮性と同値。
方針：反転と右模型の比較による両方向を合わせる。
規約：左 unstraightening を用いず、区間模型を直接検査できる。
使われ方：Kerodon §4.7.3、§6.2.6 の局所存在の区間模型での判定。 -/
lemma isInitialVertex_iff_intervalMappingSpace_isContractibleKan {X : SSet.{u}}
    [Quasicategory X] (x : X _⦋0⦌) : IsInitialVertex x ↔
      ∀ y : X _⦋0⦌, IsContractibleKan (intervalMappingSpace x y) :=
  ⟨fun h y ↦ h.intervalMappingSpace_isContractibleKan y,
    isInitialVertex_of_intervalMappingSpace_isContractibleKan x⟩

end SerrePositivity.InfinityCategories
