module

public import SerrePositivity.DifferentialGraded.Resolution.Basic
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionTriangleFamily
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPentagon
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Path
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Length

/-!
# Resolution.FixedObject

## 概要
7 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

universe u v w z t v' w' z' t' x x'

/-! ## Bimodule（旧 SerrePositivity/DifferentialGraded/Resolution/Bimodule.lean） -/

/-! # 指定dg圏解像度上の導来bimodule圏と合成

## 概要
元のunderived積dg圏上の導来bimodule圏との同値は仮定しない。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Bimodule

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ResolutionBimodule
open CategoryTheory
open BimoduleTensor
variable (A : Type u) [CommRing A] {B : Type v} {C : Type w} {E : Type z} {F : Type t}
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]

/-- 指定した解像度のunderived積上で準同型を局所化する。 -/
abbrev DerivedCategory (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :=
  DerivedBimoduleCategory A P.source Q.source

omit [DGCategory A C] [DGCategory A E] [DGCategory A F] in
def diagonal (P : KFlatDGResolution.{u, v, v'} A B) : DerivedCategory A P P :=
  (bimoduleToDerived A P.source P.source).obj (rightKFlatDiagonal A P.source).obj

def composeFunctor (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) (R : KFlatDGResolution.{u, z, z'} A E) :
    DerivedCategory A Q R ⥤ (DerivedCategory A P Q ⥤ DerivedCategory A P R) :=
  derivedBimoduleComposeFunctor A P.source Q.source R.source R.homKFlat

def rightUnitIso (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    (composeFunctor A P Q Q).obj (diagonal A Q) ≅ 𝟭 (DerivedCategory A P Q) :=
  derivedBimoduleRightUnitIso A P.source Q.source Q.homKFlat

def leftUnitFunctor (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    DerivedCategory A P Q ⥤ DerivedCategory A P Q :=
  derivedBimoduleLeftUnitFunctor A P.source Q.source Q.homKFlat

def leftUnitIso (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    leftUnitFunctor A P Q ≅ 𝟭 (DerivedCategory A P Q) :=
  derivedBimoduleLeftUnitIso A P.source Q.source Q.homKFlat

def associator (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) (R : KFlatDGResolution.{u, z, z'} A E)
    (S : KFlatDGResolution.{u, t, t'} A F)
    (M : DerivedCategory A Q R) (N : DerivedCategory A R S) :
    (composeFunctor A P Q R).obj M ⋙ (composeFunctor A P R S).obj N ≅
      (composeFunctor A P Q S).obj (((composeFunctor A Q R S).obj N).obj M) :=
  derivedBimoduleAssociator A P.source Q.source R.source S.source R.homKFlat S.homKFlat M N

lemma triangle (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) (R : KFlatDGResolution.{u, z, z'} A E)
    (M : DerivedCategory A Q R) :
    (associator A P Q Q R (diagonal A Q) M).hom ≫
        (composeFunctor A P Q R).map ((leftUnitIso A Q R).hom.app M) =
      Functor.whiskerRight (rightUnitIso A P Q).hom ((composeFunctor A P Q R).obj M) :=
  derivedBimoduleTriangle_app A P.source Q.source R.source Q.homKFlat R.homKFlat M

/-- 恒等解像度では既存の主導来合成と定義通り一致する。 -/
lemma composeFunctor_refl [Small.{u} B] [Small.{u} C] [Small.{u} E]
    (hB : localHomKFlat A B) (hC : localHomKFlat A C) (hE : localHomKFlat A E) :
    composeFunctor A (KFlatDGResolution.refl A B hB) (KFlatDGResolution.refl A C hC)
        (KFlatDGResolution.refl A E hE) =
      derivedBimoduleComposeFunctor A B C E hE := rfl

end SerrePositivity.DifferentialGraded.ResolutionBimodule
end

end Bimodule

/-! ## Coherence（旧 SerrePositivity/DifferentialGraded/Resolution/Coherence.lean） -/

/-! # 指定dg圏解像度上の五角恒等式

## 概要
指定dg圏解像度上の五角恒等式。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Coherence

noncomputable section
namespace SerrePositivity.DifferentialGraded.ResolutionBimodule
open CategoryTheory BimoduleTensor
variable (A : Type u) [CommRing A] {B : Type v} {C : Type w} {E : Type z}
  {F : Type t} {G : Type x}
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]

/-- 元のdg圏のHomにflat性を要求せず、指定解像度上の全導来因子で五角が可換。 -/
lemma pentagon (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) (R : KFlatDGResolution.{u, z, z'} A E)
    (S : KFlatDGResolution.{u, t, t'} A F) (T : KFlatDGResolution.{u, x, x'} A G)
    (X : DerivedCategory A Q R) (Y : DerivedCategory A R S) (Z : DerivedCategory A S T) :
    derivedBimodulePentagonShort A P.source Q.source R.source S.source T.source
        R.homKFlat S.homKFlat T.homKFlat X Y Z =
      derivedBimodulePentagonLong A P.source Q.source R.source S.source T.source
        R.homKFlat S.homKFlat T.homKFlat X Y Z :=
  derivedBimodulePentagon A P.source Q.source R.source S.source T.source
    R.homKFlat S.homKFlat T.homKFlat X Y Z

end SerrePositivity.DifferentialGraded.ResolutionBimodule
end

end Coherence

/-! ## FixedObjectAugmentation（旧 SerrePositivity/DifferentialGraded/Resolution/FixedObjectAugmentation.lean） -/

/-! # 対象ラベルと増大の対象写像を固定した豊穣構造

## 概要
反復列でMathlibのEnrichedCategoryをデータとして保持する。
対象Xの既存instanceを書き換えず、増大の対象写像oを全段階で固定する。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FixedObjectAugmentation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (X : Type v) (E : Type w) [DGCategory A E] (o : X → E)

structure FixedObjectAugmentation where
  category : DGCategory A X
  map (x y : X) : category.Hom x y ⟶ homObject A E (o x) (o y)
  map_id (x : X) : category.id x ≫ map x x = eId (Complex A) (o x)
  map_comp (x y z : X) : category.comp x y z ≫ map x z =
    (map x y ⊗ₘ map y z) ≫ eComp (Complex A) (o x) (o y) (o z)

namespace FixedObjectAugmentation
variable {A X E o} (S : FixedObjectAugmentation A X E o)

def toDGFunctor : letI : DGCategory A X := S.category; DGFunctor A X E := by
  letI : DGCategory A X := S.category
  exact
    { obj := o
      map := S.map
      map_id := S.map_id
      map_comp := S.map_comp }

abbrev CellIndex := Σ x : X, Σ y : X, ComplexBoundaryCell A (S.map x y)

instance cellIndexSmall [Small.{u} X] : Small.{u} S.CellIndex := inferInstance

def cells : letI : DGCategory A X := S.category; DGCellAttachment.Family A X S.CellIndex := by
  letI : DGCategory A X := S.category
  exact
    { source := fun i => i.1
      target := fun i => i.2.1
      degree := fun i => i.2.2.degree
      boundary := fun i => i.2.2.cycle }

def cellPrimitives : letI : DGCategory A X := S.category;
    DGCellAttachment.Family.PrimitiveData A X S.CellIndex S.cells E S.toDGFunctor := by
  letI : DGCategory A X := S.category
  exact
    { primitive := fun i => i.2.2.primitive
      boundary := fun i => i.2.2.boundary }

variable [Small.{u} X]

@[instance_reducible]
def attachedCategory : DGCategory A X := by
  letI : DGCategory A X := S.category
  exact ofHomObjects A X
    (S.cells.attachedHom A X S.CellIndex)
    (S.cells.attachedIdentity A X S.CellIndex)
    (S.cells.attachedComposition A X S.CellIndex)
    (S.cells.attachedComposition_left_unit A X S.CellIndex)
    (S.cells.attachedComposition_right_unit A X S.CellIndex)
    (fun a b c d => by
      rw [DGCellAttachment.Family.attachedComposition_assoc, Iso.inv_hom_id_assoc])

/-- 全境界cellを付加しても、対象ラベルXと写像oを変えない。 -/
def attach : FixedObjectAugmentation A X E o := by
  letI : DGCategory A X := S.category
  exact
    { category := S.attachedCategory
      map := S.cellPrimitives.attachedEvaluation
      map_id := S.cellPrimitives.attachedEvaluation_unit
      map_comp := S.cellPrimitives.attachedEvaluation_composition }

def transition (x y : X) : S.category.Hom x y ⟶ S.attach.category.Hom x y := by
  letI : DGCategory A X := S.category
  exact S.cells.originalHomInclusion A X S.CellIndex x y

lemma transition_id (x : X) : S.category.id x ≫ S.transition x x = S.attach.category.id x := rfl

lemma transition_comp (x y z : X) :
    S.category.comp x y z ≫ S.transition x z =
    (S.transition x y ⊗ₘ S.transition y z) ≫ S.attach.category.comp x y z := by
  let : DGCategory A X := S.category
  exact (S.cells.attachedComposition_original A X S.CellIndex x y z).symm

lemma transition_augmentation (x y : X) : S.transition x y ≫ S.attach.map x y = S.map x y := by
  let : DGCategory A X := S.category
  exact S.cellPrimitives.attachedEvaluation_original x y

lemma attach_fills (x y : X) (c : ComplexBoundaryCell A (S.map x y)) :
    ∃ t : (S.attach.category.Hom x y).X c.degree,
      (S.attach.category.Hom x y).d c.degree (c.degree + 1) t =
        (S.transition x y).f (c.degree + 1) c.cycle.val ∧
      (S.attach.map x y).f c.degree t = c.primitive := by
  let : DGCategory A X := S.category
  let i : S.CellIndex := ⟨x, y, c⟩
  refine ⟨S.cells.generatorElement A X S.CellIndex i, ?_, ?_⟩
  · exact S.cells.differential_generatorElement A X S.CellIndex i
  · exact S.cellPrimitives.attachedEvaluation_generator i

def HomKFlat : Prop := ∀ x y : X, complexKFlat A (S.category.Hom x y)

lemma attach_homKFlat (hS : S.HomKFlat) : S.attach.HomKFlat := by
  let : DGCategory A X := S.category
  intro x y
  exact S.cells.attachedHom_kFlat A X S.CellIndex hS x y

end FixedObjectAugmentation
end SerrePositivity.DifferentialGraded
end

end FixedObjectAugmentation

/-! ## FixedObjectCategory（旧 SerrePositivity/DifferentialGraded/Resolution/FixedObjectCategory.lean） -/

/-! # 固定対象の豊穣構造を独立した対象型上の主dg圏へ戻す

## 概要
固定対象の豊穣構造を独立した対象型上の主dg圏へ戻す。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FixedObjectCategory

noncomputable section
namespace SerrePositivity.DifferentialGraded.FixedObjectAugmentation
open CategoryTheory
variable {A : Type u} [CommRing A] {X : Type v} {E : Type w} [DGCategory A E] {o : X → E}

structure Objects (_S : FixedObjectAugmentation A X E o) where
  val : X

variable (S : FixedObjectAugmentation A X E o)

def objectEquiv : X ≃ S.Objects where
  toFun x := ⟨x⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := rfl

instance objectsSmall [Small.{u} X] : Small.{u} S.Objects :=
  small_of_injective (f := fun x : S.Objects => x.val) (by
    rintro ⟨x⟩ ⟨y⟩ h
    cases h
    rfl)

instance objectsDGCategory : DGCategory A S.Objects :=
  ofHomObjects A S.Objects (fun x y => S.category.Hom x.val y.val)
    (fun x => S.category.id x.val) (fun x y z => S.category.comp x.val y.val z.val)
    (fun x y => S.category.id_comp x.val y.val)
    (fun x y => S.category.comp_id x.val y.val)
    (fun w x y z => S.category.assoc w.val x.val y.val z.val)

def augmentation : DGFunctor A S.Objects E where
  obj x := o x.val
  map x y := S.map x.val y.val
  map_id x := S.map_id x.val
  map_comp x y z := S.map_comp x.val y.val z.val

lemma objects_homKFlat (hS : S.HomKFlat) : localHomKFlat A S.Objects :=
  fun x y => hS x.val y.val

end SerrePositivity.DifferentialGraded.FixedObjectAugmentation
end

end FixedObjectCategory

/-! ## FixedObjectMap（旧 SerrePositivity/DifferentialGraded/Resolution/FixedObjectMap.lean） -/

/-! # 固定対象増大の比較と境界cellの移送

## 概要
元のdg関手を対象写像に持つ比較。各段階の豊穣構造は独立したデータとして保持する。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FixedObjectMap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FixedObjectAugmentation
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A] {D : Type v} [dD : DGCategory A D]
  {E : Type w} [dE : DGCategory A E]

structure Map (S : FixedObjectAugmentation A D D id)
    (T : FixedObjectAugmentation A E E id) (F : DGFunctor A D E) where
  hom (x y : D) : S.category.Hom x y ⟶ T.category.Hom (F.obj x) (F.obj y)
  map_id (x : D) : S.category.id x ≫ hom x x = T.category.id (F.obj x)
  map_comp (x y z : D) : S.category.comp x y z ≫ hom x z =
    (hom x y ⊗ₘ hom y z) ≫ T.category.comp (F.obj x) (F.obj y) (F.obj z)
  augmentation (x y : D) : hom x y ≫ T.map (F.obj x) (F.obj y) = S.map x y ≫ F.map x y

namespace Map
variable {S : FixedObjectAugmentation A D D id} {T : FixedObjectAugmentation A E E id}
  {F : DGFunctor A D E} (M : Map S T F)

def toDGFunctor : DGFunctor A S.Objects T.Objects where
  obj x := ⟨F.obj x.val⟩
  map x y := M.hom x.val y.val
  map_id x := M.map_id x.val
  map_comp x y z := M.map_comp x.val y.val z.val

/-- 比較はcycleと指定原始元を同時に送り、境界cellの次数を保存する。 -/
def cellMap (i : S.CellIndex) : T.CellIndex := by
  refine ⟨F.obj i.1, F.obj i.2.1, i.2.2.degree,
    complexMapCycle A (M.hom i.1 i.2.1) _ i.2.2.cycle,
    (F.map i.1 i.2.1).f i.2.2.degree i.2.2.primitive, ?_⟩
  have hc := congrArg (fun f => f i.2.2.primitive)
    ((F.map i.1 i.2.1).comm i.2.2.degree (i.2.2.degree + 1))
  change (homObject A E (F.obj i.1) (F.obj i.2.1)).d _ _
    ((F.map i.1 i.2.1).f _ i.2.2.primitive) =
    (F.map i.1 i.2.1).f _ ((homObject A D i.1 i.2.1).d _ _ i.2.2.primitive) at hc
  have hb := i.2.2.boundary
  change (homObject A D i.1 i.2.1).d _ _ i.2.2.primitive = _ at hb
  rw [hb] at hc
  have hm := congrArg (fun f => f.f (i.2.2.degree + 1) i.2.2.cycle.val)
    (M.augmentation i.1 i.2.1)
  exact hc.trans hm.symm

lemma cellMap_degree (i : S.CellIndex) : (M.cellMap i).2.2.degree = i.2.2.degree := rfl

lemma cellMap_primitive (i : S.CellIndex) :
    (M.cellMap i).2.2.primitive = (F.map i.1 i.2.1).f i.2.2.degree i.2.2.primitive := rfl

end Map
end SerrePositivity.DifferentialGraded.FixedObjectAugmentation
end

end FixedObjectMap

/-! ## FixedObjectMapExtension（旧 SerrePositivity/DifferentialGraded/Resolution/FixedObjectMapExtension.lean） -/

/-! # 増大比較のcell付加後への延長

## 概要
増大比較のcell付加後への延長。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FixedObjectMapExtension

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A] {D : Type v} [dD : DGCategory A D] [Small.{u} D]
  {E : Type w} [dE : DGCategory A E] [Small.{u} E]
  {S : FixedObjectAugmentation A D D id} {T : FixedObjectAugmentation A E E id}
  {F : DGFunctor A D E} (M : Map S T F)

local notation "SD" => @FixedObjectAugmentation.category A _ D D dD id S
local notation "TD" => @FixedObjectAugmentation.category A _ E E dE id T
local notation "SI" => @FixedObjectAugmentation.CellIndex A _ D D dD id S
local notation "TI" => @FixedObjectAugmentation.CellIndex A _ E E dE id T
local notation "SC" => @FixedObjectAugmentation.cells A _ D D dD id S
local notation "TC" => @FixedObjectAugmentation.cells A _ E E dE id T

def baseExtension : letI : DGCategory A D := S.category;
    letI : DGCategory A E := T.category; DGFunctor A D ((TC).Objects A E TI) := by
  let obj := F.obj
  let m := M.hom
  let t := T.transition
  have hi : ∀ x, (SD).id x ≫ m x x = (TD).id (obj x) := M.map_id
  have hc : ∀ x y z, (SD).comp x y z ≫ m x z =
    (m x y ⊗ₘ m y z) ≫ (TD).comp (obj x) (obj y) (obj z) := M.map_comp
  have ht : ∀ x y z, (TD).comp x y z ≫ t x z =
    (t x y ⊗ₘ t y z) ≫ T.attach.category.comp x y z := T.transition_comp
  letI : DGCategory A D := S.category
  letI : DGCategory A E := T.category
  exact
    { obj := fun x => ⟨obj x⟩
      map := fun x y => m x y ≫ t (obj x) (obj y)
      map_id := fun x => by
        change (SD).id x ≫ (m x x ≫ t (obj x) (obj x)) =
          (TD).id (obj x) ≫ t (obj x) (obj x)
        rw [← Category.assoc, hi]
      map_comp := fun x y z => by
        change (SD).comp x y z ≫ (m x z ≫ t (obj x) (obj z)) = _
        rw [← Category.assoc, hc, Category.assoc, ht,
          ← Category.assoc, ← tensorHom_comp_tensorHom]
        rfl }

def extensionPrimitives : letI : DGCategory A D := S.category;
    letI : DGCategory A E := T.category;
    DGCellAttachment.Family.PrimitiveData A D SI SC
      ((TC).Objects A E TI) (baseExtension (dD := dD) (dE := dE) M) := by
  letI : DGCategory A D := S.category
  letI : DGCategory A E := T.category
  exact
    { primitive := fun i => (TC).generatorElement A E TI (cellMap (dD := dD) (dE := dE) M i)
      boundary := fun i => (TC).differential_generatorElement A E TI
        (cellMap (dD := dD) (dE := dE) M i) }

def attachedFunctor : letI : DGCategory A D := S.category;
    letI : DGCategory A E := T.category;
    DGFunctor A ((SC).Objects A D SI) ((TC).Objects A E TI) := by
  letI : DGCategory A D := S.category
  letI : DGCategory A E := T.category
  exact (extensionPrimitives (dD := dD) (dE := dE) M).extension

/-- 延長後のHom写像。対象写像は元のdg関手Fのまま。 -/
def attachedHom (x y : D) :
    S.attach.category.Hom x y ⟶ T.attach.category.Hom (F.obj x) (F.obj y) := by
  letI : DGCategory A D := S.category
  letI : DGCategory A E := T.category
  exact (attachedFunctor (dD := dD) (dE := dE) M).map ⟨x⟩ ⟨y⟩

lemma transition_attachedHom (x y : D) :
    S.transition x y ≫ M.attachedHom x y =
      M.hom x y ≫ T.transition (F.obj x) (F.obj y) := by
  let : DGCategory A D := S.category
  let : DGCategory A E := T.category
  exact (extensionPrimitives (dD := dD) (dE := dE) M).attachedEvaluation_original x y

lemma attachedHom_id (x : D) :
    S.attach.category.id x ≫ M.attachedHom x x = T.attach.category.id (F.obj x) := by
  let : DGCategory A D := S.category
  let : DGCategory A E := T.category
  exact (attachedFunctor (dD := dD) (dE := dE) M).map_id ⟨x⟩

lemma attachedHom_comp (x y z : D) :
    S.attach.category.comp x y z ≫ M.attachedHom x z =
      (M.attachedHom x y ⊗ₘ M.attachedHom y z) ≫
        T.attach.category.comp (F.obj x) (F.obj y) (F.obj z) := by
  let : DGCategory A D := S.category
  let : DGCategory A E := T.category
  exact (attachedFunctor (dD := dD) (dE := dE) M).map_comp ⟨x⟩ ⟨y⟩ ⟨z⟩

end SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map
end

end FixedObjectMapExtension

/-! ## FixedObjectGenerators（旧 SerrePositivity/DifferentialGraded/Resolution/FixedObjectGenerators.lean） -/

/-! # 固定対象cell付加の生成元と比較による像

## 概要
固定対象cell付加の生成元と比較による像。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FixedObjectGenerators

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FixedObjectAugmentation
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A] {D : Type v} [dD : DGCategory A D] [Small.{u} D]
  (S : FixedObjectAugmentation A D D id)

/-- 各境界cellの次数にある新しい生成元。 -/
def cellGenerator (i : S.CellIndex) :
    (S.attach.category.Hom i.1 i.2.1).X i.2.2.degree := by
  letI : DGCategory A D := S.category
  exact (@cells A _ D D dD id S).generatorElement A D (@CellIndex A _ D D dD id S) i

lemma attach_map_cellGenerator (i : S.CellIndex) :
    (S.attach.map i.1 i.2.1).f i.2.2.degree (S.cellGenerator i) = i.2.2.primitive := by
  let : DGCategory A D := S.category
  exact @DGCellAttachment.Family.PrimitiveData.attachedEvaluation_generator
    A _ D (@category A _ D D dD id S) (@CellIndex A _ D D dD id S) _ (@cells A _ D D dD id S)
    D dD (@toDGFunctor A _ D D dD id S) (@cellPrimitives A _ D D dD id S) i

namespace Map
variable {S} {E : Type w} [dE : DGCategory A E] [Small.{u} E]
  {T : FixedObjectAugmentation A E E id} {F : DGFunctor A D E} (M : Map S T F)

lemma attachedHom_cellGenerator (i : S.CellIndex) :
    (M.attachedHom i.1 i.2.1).f i.2.2.degree (S.cellGenerator i) =
      T.cellGenerator (M.cellMap i) := by
  let : DGCategory A D := S.category
  let : DGCategory A E := T.category
  exact (extensionPrimitives (dD := dD) (dE := dE) M).extension_generator i

end Map
end SerrePositivity.DifferentialGraded.FixedObjectAugmentation
end

end FixedObjectGenerators
