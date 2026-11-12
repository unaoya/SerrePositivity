module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentStandardFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionFlags

/-!
# 補助解像の旗から native Path への写像

概要：F1 の正規化した旗に最終頂点を加え、実際の coherent Hom の Path の旗にする。
方針：各有限集合の持ち上げた像と最終頂点を合わせ、包含を Path の射へ送る。
規約：旗の始点は最初の集合の唯一の点であり、追加した最終頂点とは異なる。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の pinched Hom と補助解像の写像空間の比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory CategoryTheory.SimplicialThickening
open scoped _root_.Simplicial

/-- 概要：解像の旗の各段に最終頂点を加えて端点付き Path にする。
方針：始点の所属と下界性は F1 の旗から取り、終点には追加した最後の頂点を使う。
規約：元の頂点番号は castSucc と ULift でそのまま持ち上げる。
使われ方：Kerodon 2.5.9（Tag 00SC） の coherent 単体の豊穣 Hom 写像を評価する入力。 -/
def resolutionFlagPath {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) (t : Fin (d + 1)) :
    SimplicialThickening.Path (ULift.up F.start.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))) where
  I := {ULift.up (Fin.last (n + 1))} ∪
    (fun j : Fin (n + 1) ↦ (ULift.up j.castSucc : ULift.{u} (Fin (n + 2)))) '' (F.sets t : Set _)
  left := Or.inr ⟨F.start, F.start_mem t, rfl⟩
  right := Or.inl rfl
  left_le z hz := by
    rcases hz with hz | ⟨j, hj, rfl⟩
    · rw [Set.mem_singleton_iff.mp hz]
      exact (Fin.castSucc_lt_last F.start).le
    · exact F.lower t j hj
  le_right z _ := Fin.le_last z.down

/-- 概要：最後以外の頂点が解像の Path に属することは元の有限集合への所属である。
方針：最終頂点の場合を除き、二重の持ち上げの単射性で像の原像を特定する。
規約：元の頂点番号で所属を述べる。
使われ方：HA 1.3.1.17 の最大頂点と切り詰めの計算。 -/
lemma mem_resolutionFlagPath_iff {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (t : Fin (d + 1)) (j : Fin (n + 1)) :
    ULift.up j.castSucc ∈ (resolutionFlagPath.{u} F t).I ↔ j ∈ F.sets t := by
  constructor
  · rintro (h | ⟨k, hk, he⟩)
    · have h' : j.castSucc = Fin.last (n + 1) := congrArg ULift.down h
      exact False.elim ((Fin.ne_of_lt (Fin.castSucc_lt_last j)) h')
    · have h' : k = j := by simpa only [ULift.up.injEq, Fin.castSucc_inj] using he
      exact h' ▸ hk
  · intro h
    exact Or.inr ⟨j, h, rfl⟩

/-- 概要：解像の旗は実際の Path の圏の単体を与える。
方針：各段を端点付き Path にし、有限集合の包含を native な射に写す。
規約：射の等式は包含の圏の射の一意性を使う。
使われ方：Kerodon 2.5.9（Tag 00SC） の解像上の単体的写像と pinched Hom の対応。 -/
def resolutionFlagPathFunctor {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) :
    (nerve (SimplicialThickening.Path (ULift.up F.start.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))) _⦋d⦌ where
  obj := resolutionFlagPath F
  map f := ⟨⟨⟨by
    intro z hz
    rcases hz with hz | ⟨j, hj, rfl⟩
    · exact Or.inl hz
    · exact Or.inr ⟨j, F.monotone_sets f.le hj, rfl⟩⟩⟩⟩
  map_id _ := InducedCategory.hom_ext (Subsingleton.elim _ _)
  map_comp _ _ := InducedCategory.hom_ext (Subsingleton.elim _ _)

/-- 概要：解像の Path の最後以外の最大頂点は元の旗の最大元である。
方針：Path の所属と元の有限集合の所属を往復し、それぞれの最大元の上界性を使う。
規約：旗の最小点と最大点を混同しない。
使われ方：HA 1.3.1.17 の解像の射影と F1 の最大頂点の比較写像の一致。 -/
lemma resolutionFlagPath_maximum {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (t : Fin (d + 1)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (resolutionFlagPath.{u} F t) = F.maxAt t := by
  apply le_antisymm
  · exact F.le_maxAt t _ ((mem_resolutionFlagPath_iff F t _).mp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum_mem (resolutionFlagPath F t)))
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.le_pathLastMaximum (resolutionFlagPath F t) _
      ((mem_resolutionFlagPath_iff F t _).mpr (F.maxAt_mem t))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
