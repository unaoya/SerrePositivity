module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentPinchedStandard
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PathMaximum

/-!
# Path の立方体の旗の最大頂点

概要：Path の旗を最終点以外の最大頂点へ送り、その値を既知の内部座標で評価する。
方針：F1 の pathLastMaximum と pathLastMaximumMap を使い、端点付き集合の所属を計算する。
規約：F1 の最大頂点の構成を再実装しない。内部点は追加した最後の頂点より前にある。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の写像空間の比較と逆向きの射の合成。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory CategoryTheory.SimplicialThickening
open scoped _root_.Simplicial

/-- 概要：内部座標を追加した最終点より前の頂点番号へ戻す。
方針：最終点より小さいという証明で Fin の上限を一つ下げる。
規約：ULift と castSucc を忘れた値を取る。
使われ方：Kerodon 2.5.9（Tag 00SC） の Path の最大頂点の番号の計算。 -/
def pathSourceCoordinate {n : ℕ} {i : Fin (n + 1)}
    (v : Set.Ioo (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) : Fin (n + 1) :=
  ⟨v.val.down.val, v.property.2⟩

/-- 概要：内部座標を前の頂点番号へ戻してから持ち上げると元に戻る。
方針：部分型・ULift・Fin の値を比較する。
規約：対象の宇宙は変えない。
使われ方：HA 1.3.1.17 の最大元の所属と内部座標の同定。 -/
lemma pathSourceCoordinate_castSucc {n : ℕ} {i : Fin (n + 1)}
    (v : Set.Ioo (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) :
    (ULift.up (pathSourceCoordinate v).castSucc : ULift.{u} (Fin (n + 2))) = v.val := by
  rfl

/-- 概要：Path の旗の各頂点で最終点以外の最大番号を取る単調写像。
方針：旗の包含を Path の包含へ送り、F1 の最大頂点の単調性を使う。
規約：旗の番号付けは任意で、降順に限らない。
使われ方：Kerodon 2.5.9（Tag 00SC） の標準 Hom の引き戻しの添字写像。 -/
def maximumFlagOrder {n : ℕ} (i : Fin (n + 1))
    (S : Finset (Set.Ioo (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))) {m : ℕ} (e : Fin m ≃ S) :
    Fin (m + 1) →o Fin (n + 1) where
  toFun t := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeFunctor
    (show (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) <
      ULift.up (Fin.last (n + 1)) from Fin.castSucc_lt_last i) S).obj ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e).obj t))
  monotone' := by
    intro t s h
    exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeFunctor (show (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) <
        ULift.up (Fin.last (n + 1)) from Fin.castSucc_lt_last i) S ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumFunctor i).map (homOfLE h)).le

/-- 概要：旗の最大頂点の上界は始点と既に現れた内部点全ての上界であることと同値。
方針：最大元の所属を端点・内部点に分け、逆向きでは各点の最大元以下の性質を使う。
規約：追加した最終点は最大を取る集合から除く。
使われ方：HA 1.3.1.17 の重複する最大頂点の検出。 -/
lemma maximumFlagOrder_le_iff {n : ℕ} (i : Fin (n + 1))
    (S : Finset (Set.Ioo (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))) {m : ℕ} (e : Fin m ≃ S)
    (t : Fin (m + 1)) (k : Fin (n + 1)) :
    maximumFlagOrder i S e t ≤ k ↔ i ≤ k ∧
      ∀ v : S, (e.symm v).val < t.val → pathSourceCoordinate v.val ≤ k := by
  let P := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeFunctor
    (show (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) <
      ULift.up (Fin.last (n + 1)) from Fin.castSucc_lt_last i) S).obj ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e).obj t)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum P ≤ k ↔ _
  constructor
  · intro h
    refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.le_pathLastMaximum P i P.left).trans h, ?_⟩
    intro v hv
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.le_pathLastMaximum P (pathSourceCoordinate v.val) ?_).trans h
    change ULift.up (pathSourceCoordinate v.val).castSucc ∈
      {x | x = ULift.up i.castSucc ∨ x = ULift.up (Fin.last (n + 1)) ∨
        ∃ hx : x ∈ Set.Ioo (ULift.up i.castSucc) (ULift.up (Fin.last (n + 1))),
          (⟨x, hx⟩ : Set.Ioo _ _) ∈ (Subtype.val : S → Set.Ioo _ _) ''
            {v | (e.symm v).val < t.val}}
    rw [pathSourceCoordinate_castSucc]
    exact Or.inr (Or.inr ⟨v.val.property, v, hv, rfl⟩)
  · rintro ⟨hik, hvk⟩
    have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum_mem P
    change ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum P).castSucc ∈
      {x | x = ULift.up i.castSucc ∨ x = ULift.up (Fin.last (n + 1)) ∨
        ∃ hx : x ∈ Set.Ioo (ULift.up i.castSucc) (ULift.up (Fin.last (n + 1))),
          (⟨x, hx⟩ : Set.Ioo _ _) ∈ (Subtype.val : S → Set.Ioo _ _) ''
            {v | (e.symm v).val < t.val}} at hm
    rcases hm with he | he | ⟨hx, v, hv, he⟩
    · have hpi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum P = i := by
        simpa only [ULift.up.injEq, Fin.castSucc_inj] using he
      exact hpi.le.trans hik
    · have hn := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum P).isLt
      have he' := congrArg (fun z : ULift.{u} (Fin (n + 2)) ↦ z.down.val) he
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum P).val = n + 1 at he'
      omega
    · have hpvVal : (pathSourceCoordinate v.val).val = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum P).val :=
        congrArg (fun z : Set.Ioo (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
          (ULift.up (Fin.last (n + 1))) ↦ z.val.down.val) he
      have hpv : pathSourceCoordinate v.val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum P := Fin.ext hpvVal
      exact hpv.symm.le.trans (hvk v hv)

/-- 概要：最大頂点の標準単体への写像は旗の最大番号の単調写像である。
方針：F1 の最大頂点の射の評価を各頂点で使う。
規約：標準単体の単体は ULift した単体圏の射として表示する。
使われ方：Kerodon 2.5.9（Tag 00SC） の立方体評価を標準 Hom の引き戻しへ直す。 -/
lemma pathLastMaximumMap_cubeFlag {n : ℕ} (i : Fin (n + 1))
    (S : Finset (Set.Ioo (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))) {m : ℕ} (e : Fin m ≃ S) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i).app (Opposite.op ⦋m⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap (show (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) <
        ULift.up (Fin.last (n + 1)) from Fin.castSucc_lt_last i) S).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e)) =
        ULift.up (SimplexCategory.mkHom (maximumFlagOrder i S e)) := by
  apply ULift.ext
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro t
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap_apply i _ t

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
