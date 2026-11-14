module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-! # 次数を区切った単一 apex の実錐単体データ

概要：図式の全単体上の錐を、指定次数までの実単体と全ての面・正番号退化条件で束ねる。
方針：図式の単体に apex を一つ前置した単体と、始頂点の一致を記録する。
規約：このデータだけから全 join 写像の存在は主張しない。使われ方：有限次数の錐の帰納。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 指定次数までの図式単体に一つの共通 apex を前置する、全実単体の整合データ。 -/
structure TruncatedJoinConeData {K X : SSet.{u}} (f : K ⟶ X) (N : ℕ) where
  apex : X _⦋0⦌
  simplex (n : ℕ) (hn : n ≤ N) (σ : K _⦋n⦌) : X _⦋n + 1⦌
  face_zero (n : ℕ) (hn : n ≤ N) (σ : K _⦋n⦌) :
    X.δ 0 (simplex n hn σ) = f.app _ σ
  first_vertex (n : ℕ) (hn : n ≤ N) (σ : K _⦋n⦌) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op (simplex n hn σ) = apex
  face_positive (n : ℕ) (hn : n + 1 ≤ N) (σ : K _⦋n + 1⦌) (i : Fin (n + 2)) :
    X.δ i.succ (simplex (n + 1) hn σ) = simplex n (by omega) (K.δ i σ)
  degeneracy_positive (n : ℕ) (hn : n + 1 ≤ N) (σ : K _⦋n⦌) (i : Fin (n + 1)) :
    X.σ i.succ (simplex n (by omega) σ) = simplex (n + 1) hn (K.σ i σ)

/-- 同じ apex と実単体を保った、より低い次数への制限。 -/
def TruncatedJoinConeData.restrict {K X : SSet.{u}} {f : K ⟶ X} {N : ℕ}
    (C : TruncatedJoinConeData f N) (M : ℕ) (hMN : M ≤ N) : TruncatedJoinConeData f M where
  apex := C.apex
  simplex n hn σ := C.simplex n (hn.trans hMN) σ
  face_zero n hn σ := C.face_zero n (hn.trans hMN) σ
  first_vertex n hn σ := C.first_vertex n (hn.trans hMN) σ
  face_positive n hn σ i := C.face_positive n (hn.trans hMN) σ i
  degeneracy_positive n hn σ i := C.degeneracy_positive n (hn.trans hMN) σ i

end SerrePositivity.InfinityCategories.Project.DerivedCategories
