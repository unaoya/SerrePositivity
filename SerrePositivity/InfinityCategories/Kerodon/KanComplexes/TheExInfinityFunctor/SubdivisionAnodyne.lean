module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornSubdivisionIso
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornFaceInclusionAnodyne
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 細分の anodyne 保存と Ex の Kan fibration 保存

概要：実際の細分は anodyne 射を保ち、Ex は Kan fibration を保つ。
方針：細分された horn を安全な面の nerve と同定し、sd⊣Ex の持ち上げ性の対応を使う。
規約：Moss arXiv:1506.04887v2 Proposition 2.19、Proposition 3.12。
原典の pairing による strong 性とは異なり、相対収縮による anodyne 性を示す。
使われ方：Ex∞ の fibration 保存と、非 Kan 基底での引き戻し比較。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Limits
open scoped _root_.Simplicial

/--
概要：正次元の horn 包含の実際の細分は anodyne である。
方針：horn の細分比較と標準細分の同型で、安全な面の nerve の包含の anodyne 性を移す。
規約：Moss 原論文 Proposition 2.19 の生成射の場合。
使われ方：Ex の Kan fibration 保存。
-/
theorem subdivisionHorn_anodyne (n : ℕ) (k : Fin (n + 2)) :
    SSet.anodyneExtensions (SSet.sd.{u}.map (SSet.horn (n + 1) k).ι) := by
  apply (SSet.anodyneExtensions.cancel_right_of_respectsIso _
    (SSet.stdSimplex.sdIso.hom.app ⦋n + 1⦌)).mp
  rw [hornSubdivisionComparison_inclusion]
  exact SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _)
    (hornFaceInclusion_anodyne (n + 1) k)

/--
概要：Ex は任意の Kan fibration を保つ。
方針：各 horn の持ち上げを、細分された horn の anodyne 性で随伴の反対側に構成する。
規約：Moss 原論文 Proposition 3.12 の一回の Ex の場合。
使われ方：有限反復と Ex∞ の Kan fibration 保存。
-/
@[kerodon 00Z4]
theorem ex_map_rlp {E B : SSet.{u}} (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p) :
    SSet.modelCategoryQuillen.J.rlp (SSet.ex.map p) := by
  intro A D i hi
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  exact (SSet.sdExAdjunction.hasLiftingProperty_iff (SSet.horn (n + 1) k).ι p).mp
    (subdivisionHorn_anodyne n k _ hp)

/--
概要：細分は任意の anodyne 射を保つ。
方針：Ex の Kan fibration 保存と、随伴の持ち上げ性の対応を使う。
規約：Moss 原論文 Proposition 2.19。strong anodyne 性の構造は指定しない。
使われ方：細分と反復 Ex の比較。
-/
@[kerodon 00Z3]
theorem subdivision_map_anodyne {A X : SSet.{u}} (i : A ⟶ X)
    (hi : SSet.anodyneExtensions i) : SSet.anodyneExtensions (SSet.sd.map i) := by
  rw [SSet.anodyneExtensions_eq_llp_rlp]
  intro E B p hp
  exact (SSet.sdExAdjunction.hasLiftingProperty_iff i p).mpr (hi _ (ex_map_rlp p hp))

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
