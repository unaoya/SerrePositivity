module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
概要：各項 injective な複体への零ホモトピーの成分を部分複体から延長する。
方針：各次数の単射に対する injective 延長を選び、対応する零ホモトピーな鎖写像を作る。
規約：延長した鎖写像は指定した鎖写像と部分複体上で一致する。
使われ方：Stacks Lemma 19.12.3 (079L)、TT §3・§8、Toën §3.2 の超限判定の後続段階。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C]
  {A B I : CochainComplex C ℤ} (u : A ⟶ B) [Mono u] [∀ n, Injective (I.X n)]

/--
概要：零ホモトピーの次数成分の injective 延長。
方針：逆向きの隣接次数だけを延長し、他の成分は零にする。
規約：各項 injectivity を使い、非有界 K-injectivity は仮定しない。
使われ方：Stacks 19.12.3、TT §3 の短完全列に沿った零ホモトピーの延長。
-/
def injectiveExtendedHomotopy {f : A ⟶ I} (h : Homotopy f 0) (i j : ℤ) : B.X i ⟶ I.X j :=
  if (ComplexShape.up ℤ).Rel j i then Injective.factorThru (h.hom i j) (u.f i) else 0

/--
概要：延長した次数成分は部分複体上で元の零ホモトピーに一致する。
方針：injective 延長の合成公式とホモトピーの次数条件を使う。
規約：全整数次数の成分等式。
使われ方：Stacks 19.12.3、TT §3 の互換性の判定。
-/
lemma comp_injectiveExtendedHomotopy {f : A ⟶ I} (h : Homotopy f 0) (i j : ℤ) :
    u.f i ≫ injectiveExtendedHomotopy u h i j = h.hom i j := by
  classical
  dsimp [injectiveExtendedHomotopy]
  split_ifs with hij
  · exact Injective.comp_factorThru _ _
  · simp [h.zero i j hij]

/--
概要：部分複体上の零ホモトピーな鎖写像は零ホモトピーな鎖写像へ延長できる。
方針：成分を延長してから dh+hd を取る。
規約：部分複体上の射だけを指定し、延長先の射は実際に構成する。
使われ方：Stacks 19.12.3、TT §3 の短完全列の商への残差の降下。
-/
lemma exists_nullHomotopic_extension {f : A ⟶ I} (h : Homotopy f 0) :
    ∃ (g : B ⟶ I), u ≫ g = f ∧ Nonempty (Homotopy g 0) := by
  classical
  let v := injectiveExtendedHomotopy u h
  refine ⟨Homotopy.nullHomotopicMap v, ?_, ⟨Homotopy.nullHomotopy v ?_⟩⟩
  · rw [Homotopy.comp_nullHomotopicMap]
    have hv : (fun i j => u.f i ≫ v i j) = h.hom := by
      funext i j
      exact comp_injectiveExtendedHomotopy u h i j
    rw [hv]
    simpa using h.sub_eq_nullHomotopicMap.symm
  · intro i j hij
    exact ite_eq_right hij

end SerrePositivity.KST.DerivedGeometry
