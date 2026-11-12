module
public import SerrePositivity.KST.SConstruction.Cofinality.WideHomotopyObjectClasses

/-!
概要：同じ全多次数の元の分母はホモトピー圏の双積射で閉じる。
方針：実安定閉包の三角的分母の有限積閉性を、標準双積の積錐で使う。
規約：一般の局所化 API を複製せず、指定完備化射の分母に特殊化する。
使われ方：wide 成分への双積演算の降下。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：同じ元の本質像による三角的分母は二つの分母射の双積を含む。
方針：分母の有限積閉性を標準双積の積錐へ適用する。
規約：ホモトピー圏の双積射そのものを扱う。
使われ方：成分上の和の両変数での辺不変性。 -/
lemma completionTrW_biprod_map (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    {a b c d : hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier}
    (g : a ⟶ b) (h : c ⟶ d)
    (hg : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val)).trW g)
    (hh : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val)).trW h) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val)).trW (biprod.map g h) := by
  let P := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (LocalizingInvariants.completionEssentialImage
    (((multiSEndofunctor r).obj ι).map f).val)
  apply MorphismProperty.limitsOfShape_le (W := P.trW) (J := Discrete WalkingPair)
  refine MorphismProperty.limitsOfShape.mk' (pair a c) (pair b d)
    (BinaryFan.mk biprod.fst biprod.snd) (BinaryFan.mk biprod.fst biprod.snd)
    (BinaryBiproduct.isLimit a c) (BinaryBiproduct.isLimit b d) (mapPair g h) ?_
      (biprod.map g h) ?_
  · intro j
    cases j with
    | mk j => cases j
              · exact hg
              · exact hh
  · intro j
    cases j with
    | mk j => cases j <;> simp

/-- 概要：元の wide の一辺のホモトピー類は同じ三角的分母に属する。
方針：元の辺の全辺条件を cofiber 分母と三角的分母の照合へ渡す。
規約：同じ元の辺の類を使う。
使われ方：成分の生成関係へ双積の分母保存を適用する。 -/
lemma completionTrW_of_wideEdge (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    {x y : (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) _⦋0⦌}
    (a : SSet.Edge x y) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val)).trW
        (Truncated.HomotopyCategory.homMk ((a.map
          (LocalizingInvariants.completionCofiberWide
            (((multiSEndofunctor r).obj ι).map f).val).ι).toTruncated)) := by
  let F := ((multiSEndofunctor r).obj ι).map f
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F.val := stableModelHom_exact F
  have he := LocalizingInvariants.stableClosure_completionEssentialImage F.val
    (multiSEndofunctor_map_isIdempotentCompletion r ι f hf).2.1
  apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_iff_trW (LocalizingInvariants.completionEssentialImage F.val)
    ((a.map (LocalizingInvariants.completionCofiberWide F.val).ι).toTruncated)).mp
  have ha : a.edge.val ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      (LocalizingInvariants.completionEssentialImage F.val) := by
    simpa only [op_id, CategoryTheory.Functor.map_id, types_id_apply]
      using a.edge.property (𝟙 ⦋1⦌)
  exact he.symm ▸ ha

/-- 概要：wide の一辺で第一対象を動かしても、固定対象との双積の成分は変わらない。
方針：元の辺の類と固定対象の恒等射の双積が分母に入ることを使う。
規約：双積は元の同じホモトピー圏で取る。
使われ方：wide 成分の和の第一変数への降下。 -/
lemma completionWideObjectClass_biprod_edge_left (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    {x y : (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) _⦋0⦌}
    (a : SSet.Edge x y)
    (b : hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier) :
    completionWideObjectClass r ι f hf ((HomotopyCategory.mk x.val : hoFunctor.obj
      (((multiSEndofunctor r).obj ι).obj Y).carrier) ⊞ b) =
      completionWideObjectClass r ι f hf ((HomotopyCategory.mk y.val : hoFunctor.obj
        (((multiSEndofunctor r).obj ι).obj Y).carrier) ⊞ b) := by
  let P := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (LocalizingInvariants.completionEssentialImage
    (((multiSEndofunctor r).obj ι).map f).val)
  let g := Truncated.HomotopyCategory.homMk ((a.map
    (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val).ι).toTruncated)
  exact completionWideObjectClass_eq_of_trW r ι f hf (biprod.map g (𝟙 b))
    (completionTrW_biprod_map r ι f g (𝟙 b)
      (completionTrW_of_wideEdge r ι f hf a) (P.trW.id_mem b))

/-- 概要：wide の一辺で第二対象を動かしても、固定対象との双積の成分は変わらない。
方針：双積の交換同型で第一変数の辺不変性に帰着する。
規約：交換同型も元のホモトピー圏の同型である。
使われ方：wide 成分の和の第二変数への降下。 -/
lemma completionWideObjectClass_biprod_edge_right (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    {x y : (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) _⦋0⦌}
    (a : SSet.Edge x y)
    (b : hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier) :
    completionWideObjectClass r ι f hf (b ⊞ (HomotopyCategory.mk x.val : hoFunctor.obj
      (((multiSEndofunctor r).obj ι).obj Y).carrier)) =
      completionWideObjectClass r ι f hf (b ⊞ (HomotopyCategory.mk y.val : hoFunctor.obj
        (((multiSEndofunctor r).obj ι).obj Y).carrier)) :=
  (completionWideObjectClass_iso r ι f hf (biprod.braiding b _)).trans
    ((completionWideObjectClass_biprod_edge_left r ι f hf a b).trans
      (completionWideObjectClass_iso r ι f hf (biprod.braiding _ b)))

end SerrePositivity.KST.SConstruction.Cofinality
