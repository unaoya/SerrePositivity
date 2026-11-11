module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionImage
public import Mathlib.Data.Finset.Sort

/-!
概要：任意の頂点集合で定める旗の解像の面とその交わり。
方針：旗の台が指定した集合に含まれる条件を使い、非空な面を小さい標準単体の解像で表す。
規約：空の頂点集合の面は空の単体集合。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面とその交わりによる有限の貼り合わせ。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：台が指定した頂点集合に入る旗からなる面。
方針：引き戻しで台が増えないことを使って部分複体にする。
規約：頂点集合 T は空でもよい。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面どうしの交わりの統一した表示。 -/
def coherentResolutionFace {n : ℕ} (T : Finset (Fin (n + 1))) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n).Subcomplex where
  obj _ := {F | F.down.support ⊆ T}
  map {a b} α F hF := (F.down.support_pullback_subset α.unop.toOrderHom).trans hF

/-- 概要：頂点集合の包含は解像の面の包含を与える。
方針：台の包含を推移させる。
規約：同じ標準単体の中の面。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面の貼り合わせ図式の射。 -/
lemma coherentResolutionFace_mono {n : ℕ} {T U : Finset (Fin (n + 1))} (h : T ⊆ U) :
    coherentResolutionFace.{u} T ≤ coherentResolutionFace U := by
  intro d F hF
  exact hF.trans h

/-- 概要：解像の二つの面の交わりは頂点集合の交わりの面。
方針：台が両方に含まれる条件を一つの交わりへの包含にまとめる。
規約：部分複体の下限で交わりを表す。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界の貼り合わせの重なり。 -/
lemma coherentResolutionFace_inter {n : ℕ} (T U : Finset (Fin (n + 1))) :
    coherentResolutionFace.{u} (T ∩ U) = coherentResolutionFace T ⊓ coherentResolutionFace U := by
  apply Subfunctor.ext
  funext d
  apply Set.ext
  intro F
  change (F.down.support ⊆ T ∩ U) ↔ (F.down.support ⊆ T ∧ F.down.support ⊆ U)
  exact Finset.subset_inter_iff

/-- 概要：空の頂点集合の解像の面は空。
方針：旗の台は始点を含むので空集合には含まれない。
規約：交わりが空の場合の基底例。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、互いに素な面の貼り合わせ。 -/
lemma coherentResolutionFace_empty (n : ℕ) :
    coherentResolutionFace.{u} (∅ : Finset (Fin (n + 1))) = ⊥ := by
  apply le_antisymm _ bot_le
  intro d F hF
  exact Finset.notMem_empty _ (hF (F.down.start_mem _))

/-- 概要：全頂点集合の面は解像全体。
方針：全ての台は全頂点集合に含まれる。
規約：部分複体の上限の元 top との等式。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、全体と面の統一した扱い。 -/
lemma coherentResolutionFace_univ (n : ℕ) :
    coherentResolutionFace.{u} (Finset.univ : Finset (Fin (n + 1))) = ⊤ := by
  apply top_unique
  intro d F _
  exact Finset.subset_univ _

/-- 概要：単射な頂点写像の解像の像は、その頂点集合で定める面。
方針：台による像の判定を有限集合の直接像の所属に読み替える。
規約：単射な写像にのみ適用する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、任意の面を小さい解像で表示する準備。 -/
lemma range_coherentResolutionMap {n m : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β) :
    Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap.{u} β) =
      coherentResolutionFace (Finset.univ.image β) := by
  classical
  apply Subfunctor.ext
  funext d
  apply Set.ext
  intro F
  change (∃ G : ULift.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d.unop.len),
    ULift.up (G.down.pushforward β) = F) ↔ F.down.support ⊆ Finset.univ.image β
  constructor
  · rintro ⟨G, hG⟩ k hk
    have hs := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.mem_range_pushforward_iff β hβ F.down).mp
      ⟨G.down, congrArg ULift.down hG⟩ k hk
    obtain ⟨j, hj⟩ := hs
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
  · intro hs
    have hsupport : ∀ k ∈ F.down.support, k ∈ Set.range β := by
      intro k hk
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hs hk)
      exact ⟨j, hj⟩
    obtain ⟨G, hG⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.mem_range_pushforward_iff β hβ F.down).mpr hsupport
    exact ⟨ULift.up G, ULift.ext hG⟩

/-- 概要：頂点集合の順序同型で与えた写像の解像の像は、その面。
方針：順序同型の全射性で頂点写像の像が指定した集合そのものと示す。
規約：T が Fin(m+1) と順序同型である表示を明示的に受け取る。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、非空な面の表現可能性の解像版。 -/
lemma range_coherentResolutionMap_of_orderIso {n m : ℕ} (T : Finset (Fin (n + 1)))
    (e : Fin (m + 1) ≃o T) :
    Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap.{u}
      ((OrderHom.Subtype.val (· ∈ T)).comp e.toOrderEmbedding.toOrderHom)) =
        coherentResolutionFace T := by
  classical
  rw [range_coherentResolutionMap _ (Subtype.val_injective.comp e.injective)]
  congr 1
  ext k
  constructor
  · intro hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
    exact (e j).property
  · intro hk
    obtain ⟨j, hj⟩ := e.surjective ⟨k, hk⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, congrArg Subtype.val hj⟩

/-- 概要：非空な頂点集合の解像の面は小さい標準単体の解像と同型。
方針：単射な頂点写像の始域と像の同型を、面としての像の計算で移す。
規約：頂点集合 T の順序同型による表示に依存した同型。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面と交わりの射影の同値性の基底。 -/
noncomputable def coherentResolutionFaceIso {n m : ℕ} (T : Finset (Fin (n + 1)))
    (e : Fin (m + 1) ≃o T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} m ≅ (coherentResolutionFace T).toSSet := by
  let β := (OrderHom.Subtype.val (· ∈ T)).comp e.toOrderEmbedding.toOrderHom
  have hβ : Function.Injective β := Subtype.val_injective.comp e.injective
  haveI := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap_mono.{u} β hβ
  exact asIso (Subcomplex.toRange (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap β)) ≪≫
    eqToIso (congrArg (fun A : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n).Subcomplex ↦ A.toSSet)
      (range_coherentResolutionMap_of_orderIso T e))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
