module

public import SerrePositivity.KST.Comparison.FreeDegeneracies
public import SerrePositivity.KST.Comparison.FatNormalFormAction
public import SerrePositivity.KST.Comparison.FatRealizationMono

/-!
# 自由な退化の標準形の計算

概要：augmentation と単体作用を全射による標準形で計算し、単射保存を証明する。
方針：fat realization の標準形の既証の式を、定数化した行へ適用する。
規約：Segal 1974 Proposition 1.6 の模型比較の準備。
使われ方：標準単体の余分な退化と、一般の単体集合へのセルによる移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial

/--
概要：augmentation は標準形の全射で元の単体を引き戻す。
方針：fat realization から対角への比較の各行の評価を使う。
規約：全射性の証拠には依存しない。
使われ方：収縮と元の単体集合への比較の計算。
-/
theorem freeDegeneraciesAugmentation_realize (X : SSet.{u}) (d : SimplexCategoryᵒᵖ)
    (p : FatNormalForm (discreteRowsFunctor.obj X) d) :
    (freeDegeneraciesAugmentation.app X).app d
      (fatNormalFormRealize (discreteRowsFunctor.obj X) d p) = X.map p.epi.op p.simplex := by
  have h := congrArg (fun t => t.app d
    (p.simplex, SSet.stdSimplex.objEquiv.{u}.symm p.epi))
    (fatRealizationInclusion_toDiagonal (discreteRowsFunctor.obj X) p.degree.len)
  change (fatRealizationToDiagonal (discreteRowsFunctor.obj X)).app d
      ((fatRealizationInclusion (discreteRowsFunctor.obj X) p.degree.len).app d
        (p.simplex, SSet.stdSimplex.objEquiv.{u}.symm p.epi)) = _
  change (fatRealizationToDiagonal (discreteRowsFunctor.obj X)).app d
      ((fatRealizationInclusion (discreteRowsFunctor.obj X) p.degree.len).app d
        (p.simplex, SSet.stdSimplex.objEquiv.{u}.symm p.epi)) =
      X.map (SSet.stdSimplex.objEquiv.{u}
        (SSet.stdSimplex.objEquiv.{u}.symm p.epi)).op p.simplex at h
  rw [Equiv.apply_symm_apply] at h
  exact h

/--
概要：自由な退化の単体作用は、標準形の全射への前合成の後の正規化である。
方針：定数単体集合の内側の作用が恒等であることを使う。
規約：前合成の射は全射とは限らない。
使われ方：新しい頂点を追加する操作の自然性の計算。
-/
theorem freeDegeneraciesNormalForm_action (X : SSet.{u})
    {d e : SimplexCategoryᵒᵖ} (θ : d ⟶ e)
    (p : FatNormalForm (discreteRowsFunctor.obj X) d) :
    freeDegeneraciesNormalForm X e ((freeDegeneracies.obj X).map θ
      (fatNormalFormRealize (discreteRowsFunctor.obj X) d p)) =
      fatNormalize (discreteRowsFunctor.obj X) e p.simplex (θ.unop ≫ p.epi) := by
  change fatDegreeNormalize (discreteRowsFunctor.obj X) e
    ((fatRealization (discreteRowsFunctor.obj X)).map θ
      (fatNormalFormRealize (discreteRowsFunctor.obj X) d p)) = _
  rw [fatDegreeNormalize_action, fatDegreeNormalize_realize]
  rfl

/--
概要：自由な退化の関手は単射を保つ。
方針：行の定数化は成分ごとの単射を保ち、fat realization の単射保存へ渡す。
規約：単体次数の元の写像に関する mono の性質。
使われ方：セルによる自然比較の可逆性の帰納。
-/
instance freeDegeneracies_preservesMonomorphisms : freeDegeneracies.{u}.PreservesMonomorphisms where
  preserves f hf := by
    apply fatRealizationMap_mono (discreteRowsFunctor.map f)
    intro n
    apply (NatTrans.mono_iff_mono_app _).mpr
    intro d
    change Mono (f.app n)
    exact (NatTrans.mono_iff_mono_app f).mp hf n

end SerrePositivity.KST.Comparison
