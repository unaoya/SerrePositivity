module

public import SerrePositivity.InfinityCategories.Core.JoinCylinderSimplex
public import SerrePositivity.InfinityCategories.Core.FatJoinFunctor

/-!
概要：fat join から通常の join への比較の自然性。
方針：円柱の単体の式で自然性を示し、二段の pushout の外延性を使う。
規約：両因子の射は任意。
使われ方：Kerodon §4.6.2 の一般の単体集合へのセルによる比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：join の円柱比較は左右の因子の射に自然。
方針：切断は区間成分だけで決まり、左右の制限は射と可換であることを使う。
規約：元の単体集合の quasicategory 性は不要。
使われ方：Kerodon §4.6.2 の fat join 比較の自然性。 -/
lemma joinCylinderMap_naturality {A A' B B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') :
    fatJoinCylinderMap f g ≫ joinCylinderMap A' B' =
      joinCylinderMap A B ≫ joinMap f g := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨a, t⟩, b⟩
  change (joinCylinderMap A' B').app (Opposite.op ⦋n⦌)
      ((f.app (Opposite.op ⦋n⦌) a, t), g.app (Opposite.op ⦋n⦌) b) =
    (joinMap f g).app (Opposite.op ⦋n⦌)
      ((joinCylinderMap A B).app (Opposite.op ⦋n⦌) ((a, t), b))
  rw [joinCylinderMap_app, joinCylinderMap_app]
  let s := (joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋n⦌) t
  refine Join.Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · change Join.augMap A' (Join.prefixIncl (n + 1) s.1.val _)
        (Join.augHom f (n + 1) a) =
      Join.augHom f s.1.val (Join.augMap A (Join.prefixIncl (n + 1) s.1.val _) a)
    exact (Join.augHom_naturality (n := n + 1) f
      (Join.prefixIncl (n + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt)) a).symm
  · change Join.augMap B' (Join.suffixIncl (n + 1) s.1.val _)
        (Join.augHom g (n + 1) b) =
      Join.augHom g (n + 1 - s.1.val) (Join.augMap B (Join.suffixIncl (n + 1) s.1.val _) b)
    exact (Join.augHom_naturality (n := n + 1) g
      (Join.suffixIncl (n + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt)) b).symm

/-- 概要：fat join と通常の join の比較は両因子の射に自然。
方針：円柱の自然性と左右の包含上の計算で比較する。
規約：任意の単体集合間の射。
使われ方：Kerodon Theorem 4.6.2.8 のセルによる比較の貼り合わせ。 -/
lemma fatJoinComparison_naturality {A A' B B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') :
    fatJoinMap f g ≫ fatJoinComparison A' B' = fatJoinComparison A B ≫ joinMap f g := by
  apply fatJoin_hom_ext
  · rw [← Category.assoc, fatJoinCylinder_map, Category.assoc, fatJoinCylinder_comparison,
      ← Category.assoc, fatJoinCylinder_comparison, joinCylinderMap_naturality]
  · rw [← Category.assoc, fatJoinInl_map, Category.assoc, fatJoinInl_comparison,
      ← Category.assoc, fatJoinInl_comparison, joinInl_joinMap]
  · rw [← Category.assoc, fatJoinInr_map, Category.assoc, fatJoinInr_comparison,
      ← Category.assoc, fatJoinInr_comparison, joinInr_joinMap]

end SerrePositivity.InfinityCategories
