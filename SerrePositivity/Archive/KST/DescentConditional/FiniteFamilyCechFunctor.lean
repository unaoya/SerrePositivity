module

public import SerrePositivity.Archive.KST.DescentConditional.FiniteFamilyCech

/-!
# 元の前層の全自然な有限被覆族 Čech

## 概要
有限被覆族の Čech と指定増強を、元の前層についても自然な関手にする。

## 方針
各引き戻しの値の自然変換を有限積で束ね、元の自然性を積射影で検査する。

## 規約
増強元と被覆族の全射を同時に保持する。前層の非交和保存は仮定しない。

## 使われ方
論文 公理 (1)、補題 3.2 の射の局所検査と Zariski Čech 降下。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w t z

open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {ι : Type z} [Finite ι] {Y : C} (X : ι → C) (cover : ∀ i, X i ⟶ Y)
  {V : Type w} [Category.{t} V] [HasFiniteProducts V]

/-- 概要：元の前層の射による被覆族 Čech 図式の実際の自然変換（公理 (1)）。
方針：各段では引き戻しの値の成分を有限積で写し、積射影で自然性を検査する。
規約：元の前層の全自然変換を使う。使われ方：前層の射の局所的な弱同値の検査。 -/
def familyCechDiagramMap {F G : Cᵒᵖ ⥤ V} (a : F ⟶ G) :
    familyCechDiagram X cover F ⟶ familyCechDiagram X cover G where
  app n := CategoryTheory.Limits.Pi.map fun b ↦ a.app (op (familyCechTerm X cover n b))
  naturality {n m} f := by
    apply Pi.hom_ext
    intro b
    simp only [Category.assoc]
    change familyCechValueMap X cover F f ≫
        CategoryTheory.Limits.Pi.map (fun c : Fin (m.len + 1) → ι ↦
          a.app (op (familyCechTerm X cover m c))) ≫
        Pi.π (fun c ↦ G.obj (op (familyCechTerm X cover m c))) b =
      CategoryTheory.Limits.Pi.map (fun c : Fin (n.len + 1) → ι ↦
          a.app (op (familyCechTerm X cover n c))) ≫
        familyCechValueMap X cover G f ≫
        Pi.π (fun c ↦ G.obj (op (familyCechTerm X cover m c))) b
    simp only [familyCechValueMap, Category.assoc, Pi.lift_comp_π,
      Pi.lift_comp_π_assoc, CategoryTheory.Limits.Pi.map_π,
      CategoryTheory.Limits.Pi.map_π_assoc]
    exact congrArg (Pi.π _ (fun j ↦ b (f.toOrderHom j)) ≫ ·)
      (a.naturality (familyCechMap X cover f b).op)

/-- 概要：有限被覆族の Čech は元の前層から増強つき余単体対象への実際の関手（公理 (1)）。
方針：段ごとの自然変換と基底での成分を、指定基底射についての自然性で束ねる。
規約：非交和保存や降下性自体は仮定しない。使われ方：公理 (1) の型と局所検査。 -/
def familyAugmentedCechFunctor : (Cᵒᵖ ⥤ V) ⥤ CosimplicialObject.Augmented V where
  obj F :=
    { left := F.obj (op Y)
      right := familyCechDiagram X cover F
      hom := familyCechAugmentation X cover F }
  map {F G} a :=
    { left := a.app (op Y)
      right := familyCechDiagramMap X cover a
      w := by
        apply NatTrans.ext
        funext n
        apply Pi.hom_ext
        intro b
        change (a.app (op Y) ≫ Pi.lift (fun c : Fin (n.len + 1) → ι ↦
            G.map (WidePullback.base (fun j ↦ cover (c j))).op)) ≫
              Pi.π (fun c ↦ G.obj (op (familyCechTerm X cover n c))) b =
          (Pi.lift (fun c : Fin (n.len + 1) → ι ↦
            F.map (WidePullback.base (fun j ↦ cover (c j))).op) ≫
            CategoryTheory.Limits.Pi.map (fun c : Fin (n.len + 1) → ι ↦
              a.app (op (familyCechTerm X cover n c)))) ≫
              Pi.π (fun c ↦ G.obj (op (familyCechTerm X cover n c))) b
        rw [Category.assoc, Pi.lift_comp_π, Category.assoc,
          CategoryTheory.Limits.Pi.map_π, ← Category.assoc, Pi.lift_comp_π]
        exact (a.naturality (WidePullback.base (fun j ↦ cover (b j))).op).symm }
  map_id F := by
    apply CommaMorphism.ext
    · rfl
    · apply NatTrans.ext
      funext n
      exact CategoryTheory.Limits.Pi.map_id
  map_comp {F G H} a b := by
    apply CommaMorphism.ext
    · rfl
    · apply NatTrans.ext
      funext n
      exact (CategoryTheory.Limits.Pi.map_comp_map
        (fun c : Fin (n.len + 1) → ι ↦ a.app (op (familyCechTerm X cover n c)))
        (fun c : Fin (n.len + 1) → ι ↦ b.app (op (familyCechTerm X cover n c)))).symm

/-- 概要：元の空間値前層の有限被覆族の指定増強つき図式（公理 (1)）。
方針：全自然な被覆族の関手を単体集合の値域で評価する。
規約：値は各引き戻しの空間の有限積。使われ方：実際の指定ホモトピー比較による Zariski 降下。 -/
abbrev familyCechSpace (F : Cᵒᵖ ⥤ SSet.{0}) : AugmentedCechDiagram SimplexCategory :=
  (familyAugmentedCechFunctor X cover).obj F

end SerrePositivity.KST.Descent
