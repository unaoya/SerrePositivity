module

public import SerrePositivity.EInfinity.Modules.TensorDoldKanHom

/-!
# 同じ加群 frame Hom と dg Hom の二変数自然な同型

概要：M10 の全単体 Hom 比較を始域・標的の両変数に自然な同型へ束ねる。
方針：既存の逆転置の始域自然性を両逆で戻し、同じ実 Dold–Kan の射へ送る。
規約：HA 1.3.1.13、Kerodon 2.5.9（Tag 00SC）、元の主 Hom end を保持する。
使われ方：元の全 probe で選択済み frame と dg Hom の両端を同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：同じ転置は元の加群の全ての始域射に自然。
方針：既存の逆転置の自然性と両逆の式を合成する。
規約：HA 1.3.1.13、全単体係数。使われ方：probe 変数の全自然性。 -/
lemma moduleParamCurry_sourceMap {K : Complex A} {M P N : ModuleCategory A D}
    (g : M ⟶ P) (f : moduleTensorLeftObj A D K P ⟶ N) :
    moduleParamCurry A D (moduleTensorLeftMap A D K g ≫ f) =
      moduleParamCurry A D f ≫ eHomWhiskerRight (Complex A) g N := by
  apply moduleParamUncurry_injective (M := M) (N := N)
  calc
    _ = moduleTensorLeftMap A D K g ≫ f := moduleParamUncurry_curry A D _
    _ = moduleTensorLeftMap A D K g ≫ moduleParamUncurry A D (moduleParamCurry A D f) :=
      congrArg (fun z => moduleTensorLeftMap A D K g ≫ z)
        (moduleParamUncurry_curry A D f).symm
    _ = _ := moduleParamUncurry_naturality_source A D g (moduleParamCurry A D f)

/-- 概要：元の主 Hom end の実 Dold–Kan を二変数の全関手にする。
方針：既存の豊穣 Hom 二関手の後で同じ smart 切断と実 Γ を作用させる。
規約：HA 1.3.1.13、両変数の全閉零射。使われ方：同じ比較の dg Hom 側の全関手。 -/
def moduleDoldKanHomBifunctor :
    (ModuleCategory A D)ᵒᵖ ⥤ ModuleCategory A D ⥤ SSet.{u} :=
  eHomFunctor (Complex A) (ModuleCategory A D) ⋙
    (Functor.whiskeringRight (ModuleCategory A D) (Complex A) SSet.{u}).obj
      (truncatedDoldKanFunctor A)

/-- 概要：同じ全単体 frame Hom は元の dg Hom の実 Dold–Kan と二変数自然に同型。
方針：同じ標的自然同型に始域射の自然性を付ける。
規約：HA 1.3.1.13、始域を離散化しない。使われ方：全 probe と全標的での端点同定。 -/
def moduleTensorHomDoldKanBifunctorIso :
    (moduleTensorSimplicesFunctor A D).op ⋙ cosimplicialHomBifunctor ≅
      moduleDoldKanHomBifunctor A D :=
  NatIso.ofComponents (fun P => moduleTensorHomDoldKanNatIso A D P.unop) (by
    intro P Q g
    apply NatTrans.ext
    funext N
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro f
    change normalizedSimplexHomEquiv A
      (moduleHom A D (ForgetEnrichment.to (Complex A) Q.unop)
        (ForgetEnrichment.to (Complex A) N)) n.unop
      (moduleParamCurry A D
        (moduleTensorLeftMap A D
          ((BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n.unop)) g.unop ≫ f)) = _
    rw [moduleParamCurry_sourceMap A D (M := Q.unop) (P := P.unop) (N := N)]
    exact normalizedSimplexHomEquiv_postcomp A n.unop (moduleParamCurry A D f)
      (eHomWhiskerRight (Complex A) g.unop N))

end SerrePositivity.EInfinity.Modules
