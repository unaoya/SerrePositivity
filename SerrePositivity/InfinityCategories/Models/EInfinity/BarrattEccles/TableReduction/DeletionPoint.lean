module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ForwardReverse
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseForward

/-!
模型。文献の定義との比較は後で
# 成功 table の削除位置の有限型

概要：Berger–Fresse §1.4.4 の相殺の添字を実際の成功出力と削除位置で束ねる。
方針：同じ Schedule の出力の一意性により、行長と全出力位置の有限型へ単射を作る。
規約：退化出力も保持し、正規化は項を評価するときに行う。
使われ方：残余の区切り削除と最終出現削除の全単射・有限和の相殺に使う。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：成功した Schedule とその実際の出力の削除位置（BF §1.4.4）。
方針：reduceRows の成功を出力とともに保持する。
規約：非全射・退化した出力も保持する。
使われ方：全 Schedule の全削除項の共通の添字。 -/
structure DeletionPoint {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n)) where
  schedule : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d
  output : List (Fin n)
  success : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w schedule) [] = some output
  position : Fin output.length

namespace DeletionPoint

variable {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}

/-- 概要：Schedule と位置の自然数値が同じ削除点は一致（BF §1.4.4）。
方針：成功出力の一意性と有限添字の外延性を使う。
規約：成功の証明項には依存しない。
使われ方：二方向の対応の逆関係を削除点の等式へ束ねる。 -/
@[ext] lemma ext (p q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint w) (hs : p.schedule = q.schedule)
    (hk : p.position.val = q.position.val) : p = q := by
  rcases p with ⟨r, out, h, k⟩
  rcases q with ⟨r', out', h', k'⟩
  dsimp only at hs hk
  subst r'
  have ho : out = out' := Option.some.inj (h.symm.trans h')
  subst out'
  have he : k = k' := Fin.ext hk
  subst k'
  rfl

/-- 概要：成功削除点を有限な Schedule と全出力位置の対で符号化（BF §1.4.4）。
方針：成功出力の長さ n+d を使い、位置だけを共通の有限添字へ移す。
規約：成功しない Schedule の対は像に含まれない。
使われ方：削除点の有限性を与える。 -/
def code (p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint w) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d × Fin (n + d) :=
  (p.schedule, ⟨p.position.val, by
    have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w p.schedule p.output p.success
    have := p.position.isLt
    omega⟩)

/-- 概要：削除点の有限符号化は単射（BF §1.4.4）。
方針：二つの成分の等式を削除点の外延性へ渡す。
規約：出力は成功から一意。
使われ方：有限型の構造を成功削除点へ移す。 -/
lemma code_injective : Function.Injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint.code (w := w)) := by
  intro p q he
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint.ext p q (congrArg Prod.fst he)
  exact congrArg (fun x : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d × Fin (n + d) => x.2.val) he

/-- 概要：全成功削除点は有限（BF §1.4.4）。
方針：有限な Schedule と共通位置の対への単射から構成する。
規約：有限列挙の計算方法は主定理には用いない。
使われ方：実際の削除項の有限和を扱う。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint.instFintype : Fintype (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint w) := Fintype.ofInjective _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint.code _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint.code_injective

/-- 概要：一文字行以外の残余位置（BF §1.4.4）。
方針：既存 singletonPositions の補集合を使う。
規約：出力長は成功から与える。
使われ方：頂点境界を除いた二種類の相殺項を指定する。 -/
def Remaining (p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint w) : Prop :=
  p.position ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singletonPositions p.schedule p.output
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w p.schedule p.output p.success)

/-- 概要：残余の区切り削除の条件（BF §1.4.4）。
方針：後に同じ値が現れる条件を既存 Caesura で指定する。
規約：正規化前の退化出力も含む。
使われ方：逆対応の始点の有限部分型。 -/
def IsCaesura (p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint w) : Prop :=
  p.Remaining ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun j : Fin p.output.length => p.output[j.val]) p.position

/-- 概要：残余の先行出現を持つ最終出現削除の条件（BF §1.4.4）。
方針：区切りでなく、以前の同値の出現があることを要求する。
規約：以前の出現がない最終出現の削除係数は零として別に扱う。
使われ方：順対応の始点の有限部分型。 -/
def IsFinal (p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint w) : Prop :=
  p.Remaining ∧ ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun j : Fin p.output.length => p.output[j.val]) p.position ∧
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin p.output.length => p.output[j.val]) p.position).Nonempty

end DeletionPoint

/-- 概要：残余の区切り削除の有限型（BF §1.4.4）。
方針：成功削除点の有限部分型。
規約：退化出力も含む。
使われ方：最終出現削除との全単射の片側。 -/
abbrev CaesuraDeletion {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n)) :=
  {p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint w // p.IsCaesura}

/-- 概要：先行出現を持つ残余の最終出現削除の有限型（BF §1.4.4）。
方針：成功削除点の有限部分型。
規約：零係数の孤立した出現を含めない。
使われ方：区切り削除との全単射のもう片側。 -/
abbrev FinalDeletion {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n)) :=
  {p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint w // p.IsFinal}

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
