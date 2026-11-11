module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionEquivalence

/-!
概要：標準単体の写像による旗の押し出し。
方針：有限部分集合の直接像を取り、最大元と正規化した引き戻しの整合性を示す。
規約：単調写像は単射でなくてもよい。区間の切断の自然性は要求しない。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、補助解像の標準単体に関する関手性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：単調写像によって旗の値域を移す。
方針：始点と各段の有限集合の直接像を取る。
規約：包含方向の旗と最小元による始点の規約を保つ。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、標準単体の写像に対する作用。 -/
def CoherentResolutionFlag.pushforward {n m d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (β : Fin (n + 1) →o Fin (m + 1)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag m d where
  start := β F.start
  sets i := (F.sets i).image β
  monotone_sets := by
    intro i j hij k hk
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_image.mpr ⟨l, F.monotone_sets hij hl, rfl⟩
  first := by rw [F.first, Finset.image_singleton]
  lower i k hk := by
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
    exact β.monotone (F.lower i l hl)

/-- 概要：単調写像による旗の押し出しは最大元を写す。
方針：最大元の上界性と直接像への所属を使う。
規約：写像が複数の点を同じ点へ写しても成立する。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、標準単体への射影の自然性。 -/
lemma CoherentResolutionFlag.maxAt_pushforward {n m d : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) (β : Fin (n + 1) →o Fin (m + 1))
    (i : Fin (d + 1)) : (F.pushforward β).maxAt i = β (F.maxAt i) := by
  apply le_antisymm
  · obtain ⟨k, hk, h⟩ := Finset.mem_image.mp ((F.pushforward β).maxAt_mem i)
    rw [← h]
    exact β.monotone (F.le_maxAt i k hk)
  · apply (F.pushforward β).le_maxAt
    exact Finset.mem_image.mpr ⟨_, F.maxAt_mem i, rfl⟩

/-- 概要：旗の押し出しは正規化した引き戻しと可換。
方針：切断点より小さい点が同じ像を持つ場合は切断点自身で置き換える。
規約：値域の写像と単体の添字の写像を区別する。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、標準単体の解像への単体的な射。 -/
lemma CoherentResolutionFlag.pushforward_pullback {n m d e : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) (β : Fin (n + 1) →o Fin (m + 1))
    (α : Fin (e + 1) →o Fin (d + 1)) :
    (F.pushforward β).pullback α = (F.pullback α).pushforward β := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext
  · exact F.maxAt_pushforward β (α 0)
  · funext i
    apply Finset.ext
    intro k
    change k ∈ ((F.sets (α i)).image β).filter
      (fun l ↦ (F.pushforward β).maxAt (α 0) ≤ l) ↔
      k ∈ ((F.sets (α i)).filter (fun l ↦ F.maxAt (α 0) ≤ l)).image β
    rw [F.maxAt_pushforward]
    constructor
    · intro hk
      obtain ⟨hk, ht⟩ := Finset.mem_filter.mp hk
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
      by_cases h : F.maxAt (α 0) ≤ l
      · exact Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨hl, h⟩, rfl⟩
      · have heq : β (F.maxAt (α 0)) = β l :=
          le_antisymm ht (β.monotone (le_of_not_ge h))
        exact Finset.mem_image.mpr ⟨F.maxAt (α 0), Finset.mem_filter.mpr
          ⟨F.monotone_sets (α.monotone (Fin.zero_le i)) (F.maxAt_mem _), le_rfl⟩, heq⟩
    · intro hk
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hl, ht⟩ := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨l, hl, rfl⟩, β.monotone ht⟩

/-- 概要：恒等写像による旗の押し出しは元の旗。
方針：有限集合の恒等直接像を計算する。
規約：値域の標準単体を固定する。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、解像の関手の恒等則。 -/
lemma CoherentResolutionFlag.pushforward_id {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) :
    F.pushforward (OrderHom.id (α := Fin (n + 1))) = F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext
  · rfl
  · funext i
    exact Finset.image_id

/-- 概要：旗の押し出しは単調写像の合成と整合する。
方針：有限集合の二重の直接像を合成の直接像にまとめる。
規約：押し出しは値域について共変。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、解像の関手の合成則。 -/
lemma CoherentResolutionFlag.pushforward_comp {n m l d : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) (β : Fin (n + 1) →o Fin (m + 1))
    (γ : Fin (m + 1) →o Fin (l + 1)) :
    (F.pushforward β).pushforward γ = F.pushforward (γ.comp β) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext
  · rfl
  · funext i
    exact Finset.image_image

/-- 概要：標準単体の単調写像は旗の解像の間の射を与える。
方針：各次数で旗の押し出しを適用し、引き戻しとの可換性を使う。
規約：次数 n,m は標準単体の値域の次数。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、補助解像の関手性。 -/
def coherentResolutionMap {n m : ℕ} (β : Fin (n + 1) →o Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex m where
  app d := ↾fun F ↦ ULift.up (F.down.pushforward β)
  naturality {a b} α := by
    apply ConcreteCategory.hom_ext
    intro F
    apply ULift.ext
    exact (F.down.pushforward_pullback β α.unop.toOrderHom).symm

/-- 概要：恒等写像による解像の射は恒等。
方針：旗の押し出しの恒等則を各次数で使う。
規約：単体集合の射の等式。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、解像の関手の恒等則。 -/
lemma coherentResolutionMap_id (n : ℕ) :
    coherentResolutionMap.{u} (OrderHom.id (α := Fin (n + 1))) =
      𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex n) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  apply ULift.ext
  exact F.down.pushforward_id

/-- 概要：解像の射は値域の単調写像の合成を保つ。
方針：旗の押し出しの合成則を各次数で使う。
規約：まず β、次に γ の順に合成する。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、解像の関手の合成則。 -/
lemma coherentResolutionMap_comp {n m l : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (γ : Fin (m + 1) →o Fin (l + 1)) :
    coherentResolutionMap.{u} β ≫ coherentResolutionMap γ =
      coherentResolutionMap (γ.comp β) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  apply ULift.ext
  exact F.down.pushforward_comp β γ

/-- 概要：標準単体の旗の解像を余単体的な単体集合にまとめる。
方針：対象を旗の解像、射を有限集合の直接像による射とする。
規約：区間の切断を余単体的にすることは要求しない。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、一般の単体集合への拡張の入力。 -/
def coherentResolutionDiagram : SimplexCategory ⥤ SSet.{u} where
  obj n := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex n.len
  map β := coherentResolutionMap β.toOrderHom
  map_id n := coherentResolutionMap_id n.len
  map_comp β γ := (coherentResolutionMap_comp β.toOrderHom γ.toOrderHom).symm

/-- 概要：最大元の射影は標準単体の写像に自然。
方針：各段の直接像の最大元を元の最大元の像として計算する。
規約：余単体的な解像から標準単体の図式への射。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、射影 ρ の標準単体に関する自然性。 -/
def coherentResolutionProjectionNat : coherentResolutionDiagram.{u} ⟶ SSet.stdSimplex where
  app n := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n.len
  naturality {n m} β := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro F
    apply stdSimplex.ext
    intro i
    exact F.down.maxAt_pushforward β.toOrderHom i

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
