module
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.DifferentialGraded.Endomorphism.Module
public import SerrePositivity.DifferentialGraded.Bimodule.Basic

/-! # 大きい標的から小さい入力への制限 Yoneda
概要：標的の Small 性を要求せず、Hom_E(p(c),e) を右 C 加群値 dg 関手へ束ねる。
方針：元の Yoneda パラメータ族を p に沿って制限し、全評価で単位・合成を照合する。
規約：Small E や Small Perf を仮定しない。使われ方：Milnor 四角形の Hom 双加群。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (E : Type w) [DGCategory R E] (p : DGFunctor R C E)

/-- 元の標的の Hom 作用を、入力圏だけに制限した全次数自然族。 -/
def dgRestrictedYonedaParam (x y : E) :
    ModuleParamTrans R C (homObject R E x y)
      (restrictModule R C E p.op (representable R x))
      (restrictModule R C E p.op (representable R y)) :=
  moduleRestrictionParam R C E p.op (yonedaExtension R x (representable R y) (𝟙 _))

/-- 大きい標的から、小さい入力上の元の Hom 右加群への実 dg 関手。 -/
def dgRestrictedYoneda : DGFunctor R E (RightModule R C) :=
  Bimodule.ofParamTrans R C E (fun e => restrictModule R C E p.op (representable R e))
    (dgRestrictedYonedaParam R C E p)
    (by
      intro x c
      change eId (Complex R) x ≫
        yonedaExtensionApp R x (representable R x) (𝟙 _) (p.op.obj c) = _
      rw [endomorphismYonedaApp]
      exact (leftRepresentable R (p.obj c.unop)).map_id x)
    (by
      intro x y z c
      change eComp (Complex R) x y z ≫
        yonedaExtensionApp R x (representable R z) (𝟙 _) (p.op.obj c) = _
      rw [endomorphismYonedaApp]
      change eComp (Complex R) x y z ≫ (leftRepresentable R (p.obj c.unop)).map x z =
        (yonedaExtensionApp R x (representable R y) (𝟙 _) (p.op.obj c) ⊗ₘ
          yonedaExtensionApp R y (representable R z) (𝟙 _) (p.op.obj c)) ≫ _
      rw [endomorphismYonedaApp, endomorphismYonedaApp]
      exact (leftRepresentable R (p.obj c.unop)).map_comp x y z)

/-- 同じ制限 Yoneda の値は、元の対象間の全 Hom 複体そのもの。 -/
lemma dgRestrictedYoneda_value (e : E) (c : C) :
    ((dgRestrictedYoneda R C E p).obj e).obj (op c) = homObject R E (p.obj c) e := rfl

/-- 同じ全 Hom 作用の入力成分は、元の共変代表加群の Hom 作用。 -/
lemma dgRestrictedYoneda_map_π (x y : E) (c : C) :
    (dgRestrictedYoneda R C E p).map x y ≫ moduleHomπ R C _ _ c =
      (leftRepresentable R (p.obj c)).map x y :=
  (Bimodule.ofParamTrans_map_π R C E _ _ _ _ x y c).trans
    (endomorphismYonedaApp R E (p.obj c) x y)

end SerrePositivity.KST.SConstruction
