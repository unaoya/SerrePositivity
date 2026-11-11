module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionFace

/-!
# 逆向きの Path と単位の Hom

概要：逆向きの Hom は空であり、同じ端点の Hom は単位対象と同型である。
方針：Path が持つ端点の不等式と、同じ端点の間の集合が一点集合であることを使う。
規約：任意の線形順序で扱う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） の豊穣関手の単位と退化した合成の検査。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.SimplicialThickening MonoidalCategory

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {J : Type v} [LinearOrder J]

/-- 概要：同じ端点の間の Path は恒等 Path に等しい。
方針：各所属点を両端点の不等式で挟む。
規約：恒等射は Mathlib の thickening のもの。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） の単位 Hom の一意性。 -/
lemma pathLoop_eq_id (a : J) (p : Path a a) :
    p = 𝟙 (SimplicialThickening.mk a) := by
  apply Path.ext
  ext x
  change x ∈ p.I ↔ x ∈ ({a} : Set J)
  constructor
  · intro hx
    exact le_antisymm (p.le_right x hx) (p.left_le x hx)
  · intro hx
    exact (Set.mem_singleton_iff.mp hx) ▸ p.left

/-- 概要：同じ端点の Hom は単位対象と同型であり、同型の射は native な豊穣単位である。
方針：単位対象への唯一の射を逆射とし、各 Path が恒等射であることを使う。
規約：単位対象は SSet の直積モノイダル構造のもの。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） の単位での前合成による検査。 -/
def pathUnitIso (a : J) : 𝟙_ SSet.{v} ≅ nerve (Path a a) where
  hom := eId SSet (SimplicialThickening.mk a)
  inv := CartesianMonoidalCategory.toUnit _
  hom_inv_id := CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
  inv_hom_id := by
    apply CategoryTheory.NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro F
    exact CategoryTheory.Functor.ext (fun t ↦ (pathLoop_eq_id a (F.obj t)).symm)

/-- 概要：native な同一端点の単位写像は同型である。
方針：単位 Hom の同型の射であることを使う。
規約：同型性を必要な検査時に局所 instance として導入できる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） の退化した合成での単位の消去。 -/
lemma pathUnit_isIso (a : J) : IsIso (eId SSet (SimplicialThickening.mk a)) := by
  change IsIso (pathUnitIso a).hom
  infer_instance

/-- 概要：逆向きの Hom から任意の単体集合への唯一の写像を構成する。
方針：各単体の最初の Path が逆の端点の不等式を与える矛盾を使う。
規約：a≤b が成り立たないことを明示する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） の全ての対象対での Hom 写像。 -/
def pathEmptyHom (a b : J) (hab : ¬ a ≤ b) (X : SSet.{v}) :
    nerve (Path a b) ⟶ X where
  app _ := ↾fun F ↦ (hab (F.obj 0).le).elim
  naturality := by
    intro m k f
    apply ConcreteCategory.hom_ext
    intro F
    exact (hab (F.obj 0).le).elim

/-- 概要：逆向きの Hom からの二つの写像は等しい。
方針：各次数の単体の存在を端点の順序で否定する。
規約：行き先は任意の単体集合。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） の逆向きの Hom の制限の検査。 -/
lemma pathEmpty_hom_ext (a b : J) (hab : ¬ a ≤ b) {X : SSet.{v}}
    (f g : nerve (Path a b) ⟶ X) : f = g := by
  apply CategoryTheory.NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro F
  exact (hab (F.obj 0).le).elim

/-- 概要：合成の二つの区間の一つが逆向きなら直積からの写像は一意である。
方針：直積の対応する成分の最初の Path の不等式を使う。
規約：二つの区間のいずれの空性でもよい。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） の順序外の三対象での合成則。 -/
lemma pathProduct_empty_hom_ext (a b c : J) (h : ¬ a ≤ b ∨ ¬ b ≤ c) {X : SSet.{v}}
    (f g : nerve (Path a b) ⊗ nerve (Path b c) ⟶ X) : f = g := by
  apply CategoryTheory.NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro F
  rcases h with h | h
  · exact (h (F.1.obj 0).le).elim
  · exact (h (F.2.obj 0).le).elim

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
