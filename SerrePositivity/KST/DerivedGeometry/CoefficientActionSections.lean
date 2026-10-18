module

public import SerrePositivity.KST.DerivedGeometry.StructureScalarAction
public import SerrePositivity.KST.DerivedGeometry.CoefficientTensorPresheaf

/-!
概要：構造層加群の自己準同型環を各開の切断の線形自己準同型環へ評価する。
方針：層の射の成分を読み、加法と逆順の合成を照合する。
規約：構造層の非可換環への忘却に由来する型の違いを明示する。
使われ方：KST D4・T1′、Toën §3.2 の係数テンソル環の局所作用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable {X : Scheme.{u}}

/--
概要：構造層加群の切断を可換な切断環上の加群として読む。
方針：環の圏への忘却前後で同じ切断の加群構造を使う。
規約：新しい作用は定義しない。
使われ方：KST D4、Toën §3.2 の切断の自己準同型環。
-/
@[instance_reducible]
def structureSectionModule (M : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (M.val.obj (.op U)) := (M.val.obj (.op U)).isModule

/--
概要：構造層加群の自己準同型環から各開の切断の線形自己準同型環への環準同型。
方針：射の各成分を取り、零・単位・和・合成を成分で確認する。
規約：自己準同型の積は左作用に対応する。
使われ方：KST D4・T1′、Toën §3.2 の H 作用の局所化。
-/
def structureSectionEnd (M : X.Modules) (U : X.Opens) :
    letI := structureSectionModule M U
    End M →+* Module.End Γ(X, U) (M.val.obj (.op U)) := by
  letI := structureSectionModule M U
  exact {
    toFun f := (f.asHom.val.app (.op U)).hom
    map_zero' := rfl
    map_one' := rfl
    map_add' := fun _ _ => rfl
    map_mul' := fun _ _ => rfl }

variable {A : Type u} [CommRing A] (a : A →+* Γ(X, ⊤))

/--
概要：切断の線形自己準同型環を基礎環 A 上の代数とする。
方針：可換な構造層の切断環上の標準代数構造を基礎環の写像で制限する。
規約：各開に固定した基礎環の作用を使う。
使われ方：KST D4・T1′、Toën §3.2 のテンソル積の普遍性。
-/
@[instance_reducible]
def structureSectionEndAlgebra (M : X.Modules) (U : X.Opens) :
    letI := structureSectionModule M U
    Algebra A (Module.End Γ(X, U) (M.val.obj (.op U))) := by
  letI := structureSectionModule M U
  exact Algebra.compHom _ (sectionBaseMap a U)

variable (H : Type u) [Ring H] [Algebra A H]

/--
概要：基礎環上で構造層の作用に一致する H 作用を各開の線形自己準同型代数へ送る。
方針：自己準同型の評価に、証明された基礎環の作用の一致を添える。
規約：作用の一致は実際の層の射の等式として入力する。
使われ方：KST D4・T1′、Toën §3.2 の係数テンソル作用の構成。
-/
def coefficientSectionAction (M : X.Modules) (ρ : H →+* End M)
    (hρ : ∀ r : A, (ρ (algebraMap A H r)).asHom = structureScalarAction a M r)
    (U : X.Opens) :
    letI := structureSectionModule M U
    letI := structureSectionEndAlgebra a M U
    H →ₐ[A] Module.End Γ(X, U) (M.val.obj (.op U)) := by
  letI := structureSectionModule M U
  letI := structureSectionEndAlgebra a M U
  exact {
    __ := (structureSectionEnd M U).comp ρ
    commutes' := fun r => by
      apply LinearMap.ext
      intro m
      exact congrArg (fun f : M ⟶ M => (f.val.app (.op U)).hom m) (hρ r) }

end SerrePositivity.KST.DerivedGeometry
