module

public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
概要：可算逆系の導来逆極限を 1−shift のファイバー三角で構成する。
方針：既存の積と区別三角の存在定理を使う。
規約：極限の存在や収束を未証明の構造体フィールドにしない。
使われ方：TT §3・§8、Toën §3.2、Stacks 13.34・36.3.3 の切断塔。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory Limits Pretriangulated
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (X : ℕ → C) (s : ∀ n, X (n + 1) ⟶ X n) [HasProduct X]

/--
概要：逆系の積上の遷移シフト。
方針：第 n 成分を第 n+1 射影と遷移射の合成にする。
規約：可算逆系の添字は自然数。
使われ方：TT §3、Stacks 13.34 の導来逆極限。
-/
def sequentialShift : (∏ᶜ X) ⟶ ∏ᶜ X :=
  Pi.lift (fun n => Pi.π X (n + 1) ≫ s n)

/--
概要：逆系の差分射 1−shift。
方針：積の恒等射から遷移シフトを引く。
規約：ファイバー三角の第 2 射となる。
使われ方：TT §3、Stacks 13.34・36.3.3 の導来逆極限。
-/
def sequentialDifference : (∏ᶜ X) ⟶ ∏ᶜ X := 𝟙 _ - sequentialShift X s

/--
概要：差分射の各射影の計算。
方針：積への持ち上げの合成公式を使う。
規約：逆系の遷移射を明示する。
使われ方：TT §3、Stacks 13.34 の逆極限の錐。
-/
lemma sequentialDifference_π (n : ℕ) :
    sequentialDifference X s ≫ Pi.π X n = Pi.π X n - Pi.π X (n + 1) ≫ s n := by
  simp [sequentialDifference, sequentialShift, Preadditive.sub_comp]

/--
概要：差分射を含むファイバー区別三角を選ぶ。
方針：前三角圏の証明済みのファイバー三角の存在定理を使う。
規約：収束やコホモロジーの計算は別に証明する。
使われ方：TT §3・§8、Stacks 13.34 の導来逆極限の三角。
-/
def sequentialLimitTriangle : Triangle C :=
  let h := distinguished_cocone_triangle₁ (sequentialDifference X s)
  Triangle.mk (Classical.choose (Classical.choose_spec h))
    (sequentialDifference X s)
    (Classical.choose (Classical.choose_spec (Classical.choose_spec h)))

/--
概要：選んだ導来逆極限三角は実際に区別三角。
方針：存在定理の証明成分を取り出す。
規約：追加公理を使わない。
使われ方：TT §3、Stacks 36.3.4 の Milnor 列。
-/
lemma sequentialLimitTriangle_distinguished : sequentialLimitTriangle X s ∈ distTriang C :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (distinguished_cocone_triangle₁ (sequentialDifference X s))))

/--
概要：遷移射と両立する積への射は差分射との合成が零。
方針：各射影で両立性を使い、積の射の一意性で結論する。
規約：任意の錐からの射についての主張。
使われ方：TT §3、Stacks 36.3.3 の切断塔への比較射。
-/
lemma comp_sequentialDifference_eq_zero {Y : C} (f : Y ⟶ ∏ᶜ X)
    (hf : ∀ n, f ≫ Pi.π X (n + 1) ≫ s n = f ≫ Pi.π X n) :
    f ≫ sequentialDifference X s = 0 := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, sequentialDifference_π]
  simp [Preadditive.comp_sub, hf]

/--
概要：両立する錐から導来逆極限のファイバーへ射が存在する。
方針：差分との合成が零であることと区別三角の Hom 完全性を使う。
規約：この段階では射の同型性や一意性は主張しない。
使われ方：TT §3、Stacks 36.3.3 の切断塔の比較射。
-/
lemma exists_lift_sequentialLimitTriangle {Y : C} (f : Y ⟶ ∏ᶜ X)
    (hf : ∀ n, f ≫ Pi.π X (n + 1) ≫ s n = f ≫ Pi.π X n) :
    ∃ g : Y ⟶ (sequentialLimitTriangle X s).obj₁,
      f = g ≫ (sequentialLimitTriangle X s).mor₁ :=
  Triangle.coyoneda_exact₂ _ (sequentialLimitTriangle_distinguished X s) f
    (comp_sequentialDifference_eq_zero X s f hf)

end SerrePositivity.KST.DerivedGeometry
