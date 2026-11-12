module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentHomSection

/-!
# 昇順の最大頂点の旗の像

概要：最大頂点の昇順の旗は始点と選んだ内部点全てをちょうど一度通る。
方針：零頂点と後続頂点の公式で有限像を計算し、終点付き集合から元の集合を回収する。
規約：像は Fin の頂点番号の有限集合として取る。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の二射の合成の成分の添字の同定。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：昇順の最大番号の旗の像は始点と全内部座標の像である。
方針：各頂点を零か後続頂点に分け、逆に各座標の番号を選ぶ。
規約：空の内部座標集合も含む。
使われ方：Kerodon 2.5.9（Tag 00SC） の単射な引き戻しの像の集合の計算。 -/
lemma maximumFlagOrder_image {n : ℕ} (a : Fin (n + 1))
    (S : Finset (Set.Ioo (ULift.up a.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))) {m : ℕ} (e : Fin m ≃ S) (he : StrictMono e) :
    Finset.univ.image (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder a S e) = insert a (S.image _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSourceCoordinate) := by
  ext z
  constructor
  · intro hz
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hz
    induction t using Fin.cases with
    | zero => exact Finset.mem_insert.mpr (Or.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder_zero a S e))
    | succ j =>
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨(e j).val, (e j).property, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder_succ_of_strictMono a S e he j).symm⟩)
  · intro hz
    rcases Finset.mem_insert.mp hz with hza | hz
    · exact Finset.mem_image.mpr
        ⟨0, Finset.mem_univ _, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder_zero a S e).trans hza.symm⟩
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      refine Finset.mem_image.mpr ⟨(e.symm ⟨v, hv⟩).succ, Finset.mem_univ _, ?_⟩
      simpa using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder_succ_of_strictMono a S e he (e.symm ⟨v, hv⟩)

/-- 概要：最終点を加えた集合の内部座標に最小点を戻すと元の頂点集合になる。
方針：内部座標の所属を元の集合へ戻し、最小点以外の頂点を内部点として再構成する。
規約：J は非空で、最小点の証明は指定したものを使う。
使われ方：HA 1.3.1.17 の比較成分の添字を元の標準 Hom の成分へ戻す。 -/
lemma withLast_interior_source_image {n : ℕ} (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) :
    insert (J.min' hJ)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J)
        (J.min' hJ).castSucc (Fin.last (n + 1))).image _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSourceCoordinate) = J := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact J.min'_mem hJ
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      have hv' := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_coherentInteriorSet _ _ _ v).mp hv
      obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hv'
      have hev : t = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSourceCoordinate v).castSucc := by
        exact congrArg ULift.down (he.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSourceCoordinate_castSucc v).symm)
      rw [hev] at ht
      rcases Finset.mem_insert.mp ht with ht | ht
      · exact False.elim ((Fin.ne_of_lt (Fin.castSucc_lt_last _)) ht)
      · obtain ⟨j, hj, he⟩ := Finset.mem_image.mp ht
        exact (Fin.castSucc_injective _ he) ▸ hj
  · intro hz
    by_cases he : z = J.min' hJ
    · exact Finset.mem_insert.mpr (Or.inl he)
    · have hmin : J.min' hJ < z := lt_of_le_of_ne ((J.isLeast_min' hJ).2 hz) (Ne.symm he)
      let v : Set.Ioo (ULift.up (J.min' hJ).castSucc : ULift.{u} (Fin (n + 2)))
          (ULift.up (Fin.last (n + 1))) :=
        ⟨ULift.up z.castSucc, hmin, Fin.castSucc_lt_last z⟩
      refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨v, ?_, rfl⟩)
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_coherentInteriorSet _ _ _ v).mpr (Finset.mem_image.mpr
        ⟨z.castSucc, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨z, hz, rfl⟩), rfl⟩)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
