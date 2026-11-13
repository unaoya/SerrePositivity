module

public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
概要：単体集合の有限部分複体は非空な filtered 半順序をなす。
方針：空部分複体と二つの有限部分複体の合併を使う。
規約：有限性は非退化単体全体についてのもの。
使われ方：一般の単体集合を有限部分複体の filtered 余極限として表示する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：有限な二つの部分複体の合併は有限。
方針：二元の添字集合に対する有限上限の有限性を使う。
規約：共通部分について仮定しない。使われ方：有限部分複体の directed 性。 -/
lemma finite_subcomplex_sup {X : SSet.{u}} (A B : X.Subcomplex)
    [SSet.Finite A] [SSet.Finite B] : SSet.Finite (A ⊔ B : X.Subcomplex) := by
  have h : ∀ b : Bool, SSet.Finite (bif b then A else B : X.Subcomplex) := by
    intro b
    cases b <;> dsimp only [Bool.cond_false, Bool.cond_true] <;> infer_instance
  have hs := (SSet.finite_iSup_iff (A := fun b : Bool ↦ bif b then A else B)).2 h
  simpa only [iSup_bool_eq, Bool.cond_true, Bool.cond_false] using hs

/-- 概要：単体集合の有限部分複体の型。
方針：部分複体の半順序を有限性の部分型へ制限する。
規約：元の包含を順序として保持する。使われ方：filtered 余極限の添字圏。 -/
abbrev FiniteSubcomplex (X : SSet.{u}) := {A : X.Subcomplex // SSet.Finite A}

/-- 概要：有限部分複体として指定した対象は有限。
方針：部分型の有限性の証明を使う。
規約：部分複体を単体集合として扱う。使われ方：有限表示性による因子分解。 -/
instance finite_finiteSubcomplex {X : SSet.{u}} (A : FiniteSubcomplex X) :
    SSet.Finite A.val := A.property

/-- 概要：空部分複体は有限。
方針：初対象との同型で有限性を移す。
規約：X の頂点の存在は不要。使われ方：有限部分複体の添字の非空性。 -/
lemma finite_subcomplex_bot (X : SSet.{u}) : SSet.Finite (⊥ : X.Subcomplex) :=
  SSet.finite_of_iso (initialIsInitial.uniqueUpToIso Subcomplex.isInitialBot)

/-- 概要：有限部分複体の添字は空でない。
方針：空部分複体を指定する。
規約：元の単体集合が空でもよい。使われ方：filtered な添字の非空条件。 -/
instance finiteSubcomplex_nonempty (X : SSet.{u}) : Nonempty (FiniteSubcomplex X) :=
  ⟨⟨⊥, finite_subcomplex_bot X⟩⟩

/-- 概要：有限部分複体の包含順序は filtered な圏。
方針：合併を共通上界に取り、平行射は半順序の一意性で等化する。
規約：図式の射は元の部分複体の包含。使われ方：有限データの一段への因子分解。 -/
instance finiteSubcomplex_isFiltered (X : SSet.{u}) : IsFiltered (FiniteSubcomplex X) where
  cocone_objs A B := by
    let U : FiniteSubcomplex X := ⟨A.val ⊔ B.val, finite_subcomplex_sup A.val B.val⟩
    have hA : A ≤ U := show A.val ≤ A.val ⊔ B.val from le_sup_left
    have hB : B ≤ U := show B.val ≤ A.val ⊔ B.val from le_sup_right
    exact ⟨U, homOfLE hA, homOfLE hB, trivial⟩
  cocone_maps _ _ _ _ := ⟨_, 𝟙 _, Subsingleton.elim _ _⟩
  nonempty := inferInstance

end SerrePositivity.InfinityCategories.Project.FilteredExchange
