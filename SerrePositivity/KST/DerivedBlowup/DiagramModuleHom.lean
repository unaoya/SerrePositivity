module

public import SerrePositivity.KST.DerivedBlowup.DGEndMonoid
public import SerrePositivity.DifferentialGraded.Complexes.Zero
public import Mathlib.CategoryTheory.Category.Preorder

/-!
概要：KST §3.1 の dg 代数図式の全 diagram-module を表す dg 圏の Hom の候補。
方針：包含 i≤j に対する Hom を目標の代数にし、存在しない矢には零複体を置く。
規約：この段階では Hom・単位・合成の具体式だけを構成し、圏法則は別に検証する。
使われ方：全 diagram-module を dg 加群として導来化する係数 dg 圏。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open DifferentialGraded
open scoped ZeroObject

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]

/-- 概要：dg 代数図式の包含に対応する Hom 複体。
方針：i≤j のとき目標の代数、それ以外は零複体とする。
規約：KST §3.1。使われ方：diagram-module の係数 dg 圏の Hom。 -/
def diagramModuleHom (F : J ⥤ Mon (Complex R)) (i j : J) : Complex R :=
  if i ≤ j then (F.obj j).X else 0

/-- 概要：包含に沿う Hom 複体を目標代数と同定する。
方針：包含条件で定義の分岐を解消する。
規約：KST §3.1。使われ方：単位・合成の式の型の照合。 -/
theorem diagramModuleHom_of_le (F : J ⥤ Mon (Complex R)) {i j : J} (h : i ≤ j) :
    diagramModuleHom F i j = (F.obj j).X := ite_eq_left h

/-- 概要：目標代数から包含に対応する Hom 複体への標準同定射。
方針：包含による Hom の等式の逆を使う。
規約：KST §3.1。使われ方：合成の具体式の表示。 -/
def diagramModuleHomInclusion (F : J ⥤ Mon (Complex R)) {i j : J} (h : i ≤ j) :
    (F.obj j).X ⟶ diagramModuleHom F i j := eqToHom (diagramModuleHom_of_le F h).symm

/-- 概要：diagram-module 係数圏の各対象の単位射。
方針：元の dg 代数の単位を反射的包含の Hom に送る。
規約：KST §3.1。使われ方：係数 dg 圏の恒等射。 -/
def diagramModuleId (F : J ⥤ Mon (Complex R)) (i : J) : 𝟙_ (Complex R) ⟶ diagramModuleHom F i i :=
  MonObj.one (X := (F.obj i).X) ≫ diagramModuleHomInclusion F (le_refl i)

/-- 概要：diagram-module 係数圏の二つの Hom の合成。
方針：包含が二つとも存在するとき最初の係数を次の環へ送り目標で掛け、それ以外は零。
規約：KST §3.1。使われ方：係数 dg 圏の圏法則の検証。 -/
def diagramModuleComp (F : J ⥤ Mon (Complex R)) (i j k : J) :
    diagramModuleHom F i j ⊗ diagramModuleHom F j k ⟶ diagramModuleHom F i k := by
  by_cases hij : i ≤ j
  · by_cases hjk : j ≤ k
    · exact (eqToHom (diagramModuleHom_of_le F hij) ⊗ₘ
        eqToHom (diagramModuleHom_of_le F hjk)) ≫
        ((F.map (homOfLE hjk)).hom ⊗ₘ 𝟙 _) ≫ MonObj.mul ≫
        diagramModuleHomInclusion F (hij.trans hjk)
    · exact 0
  · exact 0

/-- 概要：二つの包含があるときの合成の具体式。
方針：Hom の同定射と合成の分岐を同時に簡約する。
規約：KST §3.1。使われ方：dg 圏の単位・結合律を代数図式の法則へ戻す。 -/
theorem diagramModuleComp_on_le (F : J ⥤ Mon (Complex R)) {i j k : J}
    (hij : i ≤ j) (hjk : j ≤ k) :
    (diagramModuleHomInclusion F hij ⊗ₘ diagramModuleHomInclusion F hjk) ≫
        diagramModuleComp F i j k =
      ((F.map (homOfLE hjk)).hom ⊗ₘ 𝟙 _) ≫ MonObj.mul ≫
        diagramModuleHomInclusion F (hij.trans hjk) := by
  simp only [diagramModuleComp, dite_eq_left hij, dite_eq_left hjk]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [diagramModuleHomInclusion, eqToHom_trans, eqToHom_refl,
    tensorHom_id, id_whiskerRight, Category.id_comp]

end SerrePositivity.KST.DerivedBlowup
