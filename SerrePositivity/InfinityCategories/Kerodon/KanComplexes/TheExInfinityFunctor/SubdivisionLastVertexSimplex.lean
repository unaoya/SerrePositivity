module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionLastVertexMap

/-!
# 細分の最終頂点写像の標準単体上の計算

概要：随伴で構成した最終頂点写像を、細分された標準単体からの射で計算する。
方針：制限 Yoneda 随伴の Hom 同値の成分の式を使う。
規約：Moss 2020 §3 の標準単体の最終頂点と全対象の写像の整合。
使われ方：二重細分から horn への候補の境界の計算。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Opposite

/--
概要：各単体からの細分された射で、最終頂点写像は明示的な標準単体の式に一致する。
方針：Ex の単位との随伴の等式を各単体で評価する。
規約：標準同型 sd(Δ[n])≅sdΔ[n] の向きは inv を前合成する向き。
使われ方：標準単体と horn の包含に関する細分の比較。
-/
theorem subdivisionLastVertexMap_on_simplex (X : SSet.{u}) (n : SimplexCategory)
    (s : X.obj (op n)) :
    SSet.stdSimplex.sdIso.inv.app n ≫ SSet.sd.map (SSet.yonedaEquiv.symm s) ≫
      subdivisionLastVertexMap.app X = subdivisionLastVertexAt n ≫ SSet.yonedaEquiv.symm s := by
  have h : (SSet.sdExAdjunction.homEquiv X X) (subdivisionLastVertexMap.app X) = exUnitAt X := by
    exact (SSet.sdExAdjunction.homEquiv X X).apply_symm_apply (exUnitAt X)
  have he := congrArg (fun f : X ⟶ SSet.ex.obj X => f.app (op n) s) h
  have hc : ((SSet.sdExAdjunction.homEquiv X X) (subdivisionLastVertexMap.app X)).app (op n) s =
      ULift.up (SSet.stdSimplex.sdIso.inv.app n ≫ SSet.sd.map (SSet.yonedaEquiv.symm s) ≫
        subdivisionLastVertexMap.app X) :=
    Presheaf.uliftYonedaAdjunction_homEquiv_app.{0} SSet.sd.{u}
      SSet.stdSimplex.sdIso.{u}.inv (subdivisionLastVertexMap.app X) s
  exact congrArg ULift.down (hc.symm.trans he)

/--
概要：標準単体上の最終頂点写像は、標準細分の同型と明示的な最終頂点の合成に等しい。
方針：標準単体の恒等写像に対応する単体で成分の計算式を評価する。
規約：二重細分で使う標準同型の向きを明示する。
使われ方：標準単体の包含と細分比較の整合。
-/
theorem subdivisionLastVertexMap_stdSimplex (n : SimplexCategory) :
    subdivisionLastVertexMap.{u}.app (SSet.stdSimplex.obj n) =
      SSet.stdSimplex.sdIso.hom.app n ≫ subdivisionLastVertexAt n := by
  have h := subdivisionLastVertexMap_on_simplex (SSet.stdSimplex.{u}.obj n) n
    (SSet.yonedaEquiv (𝟙 _))
  simp only [Equiv.symm_apply_apply, SSet.sd.map_id, Category.comp_id] at h
  exact (Iso.inv_comp_eq (SSet.stdSimplex.sdIso.app n)).mp h

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
