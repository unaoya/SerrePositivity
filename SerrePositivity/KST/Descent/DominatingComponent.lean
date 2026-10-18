module

public import SerrePositivity.KST.Descent.IrreducibleComponents
public import SerrePositivity.KST.Descent.SchemeFacts

/-!
# 整な基底を支配する被約既約成分

## 概要
既約な基底への固有全射から、基底に全射な被約既約成分を選ぶ。

## 方針
基底の生成点を持ち上げ、その点を含む成分の像が閉であることを使う。

## 規約
有限全射降下や平坦化を仮定しない。成分は元の有限型の圏内の整な閉部分スキーム。

## 使われ方
論文 補題 3.3 の整な基底への有限全射の平坦化を施す成分の選択。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.Descent

/-- 概要：固有射の像が基底の生成点を含めば全射（論文 補題 3.3）。
方針：生成点から全点への特殊化と固有射の閉像性を使う。
規約：基底の既約性を要求し、被約性や Noether 性は不要。
使われ方：支配する成分の全射性の判定。 -/
theorem surjective_of_proper_genericPoint_mem_range {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [IrreducibleSpace Y]
    (hη : genericPoint Y ∈ Set.range f) : Surjective f :=
  ⟨fun y ↦ (genericPoint_specializes y).mem_closed f.isClosedMap.isClosed_range hη⟩

variable {S : Scheme.{u}} {X Y : FiniteTypeSchemes S} (f : X ⟶ Y)

/-- 概要：被約既約成分から元の基底への指定射（論文 補題 3.3）。
方針：元の有限型の圏内の実際の閉包含と元の射を合成する。
規約：成分の選択に群作用や降下の仮定を含めない。
使われ方：整な有限全射の平坦化に使う射。 -/
noncomputable def integralComponentMap (c : IrreducibleComponentIndex X) :
    integralComponent X c ⟶ Y := integralComponentInclusion X c ≫ f

/-- 概要：有限射の被約既約成分からの指定射は有限（論文 補題 3.3）。
方針：実際の閉埋め込みと有限射の合成を使う。
規約：元の始域が被約であることは要求しない。
使われ方：平坦化する射の有限性を供給する。 -/
theorem integralComponentMap_isFinite [IsFinite f.hom.left]
    (c : IrreducibleComponentIndex X) : IsFinite (integralComponentMap f c).hom.left := by
  change IsFinite ((integralComponentInclusion X c).hom.left ≫ f.hom.left)
  infer_instance

/-- 概要：既約基底への固有全射には基底を支配する被約既約成分がある（論文 補題 3.3）。
方針：生成点の持ち上げを含む成分を選び、閉像性から全射性を得る。
規約：Noether 性や成分の有限個性は不要。実際の整な閉部分スキームを使用する。
使われ方：有限全射から平坦化する整な成分を選ぶ。 -/
theorem exists_surjective_integralComponent [IsProper f.hom.left] [Surjective f.hom.left]
    [IrreducibleSpace Y.obj.left] :
    ∃ c : IrreducibleComponentIndex X, Surjective (integralComponentMap f c).hom.left := by
  obtain ⟨x, hx⟩ := f.hom.left.surjective (genericPoint Y.obj.left)
  let c : IrreducibleComponentIndex X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have hxC : x ∈ Set.range (integralComponentInclusion X c).hom.left := by
    rw [range_integralComponentInclusion]
    exact mem_irreducibleComponent
  obtain ⟨z, hz⟩ := hxC
  have : IsProper (integralComponentMap f c).hom.left := by
    change IsProper ((integralComponentInclusion X c).hom.left ≫ f.hom.left)
    infer_instance
  refine ⟨c, surjective_of_proper_genericPoint_mem_range (integralComponentMap f c).hom.left ?_⟩
  refine ⟨z, ?_⟩
  change f.hom.left ((integralComponentInclusion X c).hom.left z) = _
  exact (congrArg f.hom.left hz).trans hx

/-- 概要：整基底への有限全射から平坦化する整な有限全射成分を得る（論文 補題 3.3）。
方針：生成点を支配する成分の全射性と、閉包含による有限性を組み合わせる。
規約：指定射は元の有限型の圏内にあり、平坦化の存在はまだ要求しない。
使われ方：Fitting 版平坦化と有限忠実平坦な細分の入力。 -/
theorem exists_finite_surjective_integralComponent [IsFinite f.hom.left] [Surjective f.hom.left]
    [IsIntegral Y.obj.left] :
    ∃ c : IrreducibleComponentIndex X,
      IsIntegral (integralComponent X c).obj.left ∧
        IsFinite (integralComponentMap f c).hom.left ∧
        Surjective (integralComponentMap f c).hom.left := by
  obtain ⟨c, hc⟩ := exists_surjective_integralComponent f
  exact ⟨c, inferInstance, integralComponentMap_isFinite f c, hc⟩

end SerrePositivity.KST.Descent
