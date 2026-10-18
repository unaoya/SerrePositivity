module

public import SerrePositivity.DifferentialGraded.Module.RestrictionCoherence
public import SerrePositivity.DifferentialGraded.Functor.Opposite

/-!
概要：KST §3.1 の補助係数圏の raw 加群に対する局所制限合成同型。
方針：値域の主 Hom end を作らず、局所源の閉零圏で同型族を構成する。
規約：small 仮定は局所源にのみ要求し、補助係数圏には追加しない。
使われ方：構造図式加群の局所評価と補助 representable の直接制限の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite
open DifferentialGraded

variable (R : Type u) [CommRing R]
variable {C : Type v} {D : Type w} {E : Type z}
  [DGCategory R C] [DGCategory R D] [DGCategory R E] [Small.{u} C]

/-- 概要：raw dg 加群の反復制限と直接制限を局所源で同型にする。
方針：各成分に恒等同型を使い、全 Hom 自然性を合成の結合則で示す。
規約：KST §3.1。使われ方：大きい補助係数圏の representable を局所比較する。 -/
def rawModuleRestrictionCompIso (F : DGFunctor R Cᵒᵖ Dᵒᵖ) (G : DGFunctor R Dᵒᵖ Eᵒᵖ)
    (M : RightModule R E) :
    ForgetEnrichment.of (Complex R) (restrictModule R C D F (restrictModule R D E G M)) ≅
      ForgetEnrichment.of (Complex R) (restrictModule R C E (F.comp G) M) :=
  moduleIsoMk R C (fun _ => Iso.refl _) (by
    intro x y
    apply hom_naturality_of_apply
    intro p f
    simp only [Iso.refl_hom, CochainComplex.HomComplex.Cochain.comp_id,
      CochainComplex.HomComplex.Cochain.id_comp]
    change (F.map x y ≫ (G.map (F.obj x) (F.obj y) ≫
      M.map (G.obj (F.obj x)) (G.obj (F.obj y)))).f p f =
      ((F.map x y ≫ G.map (F.obj x) (F.obj y)) ≫
        M.map (G.obj (F.obj x)) (G.obj (F.obj y))).f p f
    rw [Category.assoc])

/-- 概要：指定の合成 dg 遷移に沿う raw 右加群の局所制限合成同型。
方針：指定合成等式に沿って移し、二重 opposite と raw 制限合成同型を使う。
規約：KST §3.1。使われ方：元の係数圏を保持した構造加群の局所比較。 -/
def rawTransitionRestrictionCompIso (F : DGFunctor R C D) (G : DGFunctor R D E)
    (H : DGFunctor R C E) (h : F.comp G = H) (M : RightModule R Eᵒᵖ) :
    ForgetEnrichment.of (Complex R)
      (restrictModule R Cᵒᵖ Dᵒᵖ F.op.op (restrictModule R Dᵒᵖ Eᵒᵖ G.op.op M)) ≅
      ForgetEnrichment.of (Complex R) (restrictModule R Cᵒᵖ Eᵒᵖ H.op.op M) := by
  subst H
  simpa only [DGFunctor.op_comp] using rawModuleRestrictionCompIso R F.op.op G.op.op M

end SerrePositivity.KST.DerivedBlowup
