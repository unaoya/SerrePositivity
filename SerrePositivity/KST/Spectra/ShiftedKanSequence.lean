module

public import SerrePositivity.KST.Spectra.KanSequence

/-!
概要：Kan 列とその厳密な射の一段の添字移動。
方針：各段と構造射を一段先へずらす。
規約：構造射の単射性を要求しない。
使われ方：BF 1978 §2、HA §1.4.2。符号を変えた loop 列の次数の調整。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.KanSequence

/-- 概要：Kan 列の零段を落とした列。
方針：一段先の段と構造射を使う。
規約：元の構造射に単射性を仮定しない。
使われ方：BF 1978 §2。置換前の loop 列の添字移動。 -/
def tail (X : KanSequence.{u}) : KanSequence.{u} where
  level n := X.level (n + 1)
  sigma n := X.sigma (n + 1)

/-- 概要：Kan 列の厳密な射の各段も一段先へずらす。
方針：元の成分と構造可換式を再添字づけする。
規約：厳密な構造可換性を保つ。
使われ方：HA §1.4.2。符号を変えた loop 模型の比較射の添字移動。 -/
def tailHom {X Y : KanSequence.{u}} (f : Hom X Y) : Hom (tail X) (tail Y) where
  app n := f.app (n + 1)
  comm n := f.comm (n + 1)

/-- 概要：Ω 条件は Kan 列の一段の添字移動で保たれる。
方針：元の一段先の随伴構造射の条件を使う。
規約：全基点・全次数の同型性をそのまま移す。
使われ方：BF 1978 §2。符号を変えた loop 列の BF 置換への入力。 -/
theorem tail_omegaCondition {X : KanSequence.{u}} (hX : X.OmegaCondition) :
    (tail X).OmegaCondition := fun n => hX (n + 1)

end SerrePositivity.KST.Spectra.KanSequence
