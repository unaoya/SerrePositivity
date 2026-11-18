module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.UnitCoalgebra

/-!
模型。文献の定義との比較は後で
# 区間の端点と収縮の余代数射

概要：Berger–Fresse §3.1 の区間の端点・収縮を実際の P 余代数の射にする。
方針：区間の保存図式を単位余代数の余演算と照合する。
規約：区間と同じ augmentation を単位余代数へ用いる。
使われ方：convolution の前合成から代数の自然な評価射・定数射を得る。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval

open _root_.CategoryTheory

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A} {ε : P ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeOperad A}

/-- 概要：区間の指定端点は単位余代数からの射（BF §3.1）。
方針：区間の端点の余演算保存をそのまま用いる。
規約：始点と終点を Bool で指定する。
使われ方：convolution の端点評価を代数射にする。 -/
def endpointHom (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval ε) (b : Bool) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoalgebra ε ⟶ I.coalgebra where
  hom := I.endpoint b
  comm := I.endpoint_coaction b

/-- 概要：区間の収縮は単位余代数への射（BF §3.1）。
方針：区間の収縮の余演算保存を射の保存則の向きへ戻す。
規約：底の射は指定済みの収縮と同じ。
使われ方：convolution の定数関数への射を代数射にする。 -/
def contractionHom (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval ε) : I.coalgebra ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoalgebra ε where
  hom := I.contraction
  comm n := (I.contraction_coaction n).symm

/-- 概要：端点と収縮の合成は単位余代数の恒等射（BF §3.1）。
方針：底の射の等式で判定し区間の三角形を使う。
規約：両端点について同じ式を用いる。
使われ方：代数の定数射と端点評価の三角形を保証する。 -/
lemma endpointHom_contractionHom (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval ε) (b : Bool) :
    I.endpointHom b ≫ I.contractionHom = 𝟙 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoalgebra ε) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraHom.ext (I.endpoint_contraction b)

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval
