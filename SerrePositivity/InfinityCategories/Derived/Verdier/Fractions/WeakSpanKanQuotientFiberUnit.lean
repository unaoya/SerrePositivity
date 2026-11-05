module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanKanFiberUnit
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanKanQuotientDescent
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakIdentityQuotientPoint
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningFiber
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallStraighteningUnitTransformation
public import SerrePositivity.InfinityCategories.F2.Compact.SpaceEdgeValueEquivalence

/-!
概要：商上の小さい unstraightening の各 fiber と元の Kan span 値の指定比較。
方針：元の降下同型の同じ成分を Kan 値の実同値に読み戻し、fiber 値同値に合成する。
規約：全族写像の存在や fiber ごとの選択の自然性は主張しない。
使われ方：K-B-S の全族写像に要求する制限と恒等点を固定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌) (c : TransportSimplexCategory B.obj)

/-- 概要：元の降下同型の同じ成分を表す実際の空間辺。
方針：ホモトピー圏の射を表す辺を選ぶ。
規約：両端は元の商頂点と同じ strict Kan 値。
使われ方：fiber の値を元の図式へ戻す。 -/
def weakSpanKanQuotientValueEdge : SpaceInfinity.{u}.Edge
    ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x).app (Opposite.op ⦋0⦌)
      (ULift.up (q.hom.app (Opposite.op ⦋0⦌)
        ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)))))
    (spaceInfinityVertex ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanDiagram i x).obj c)) :=
  SSet.Edge.ofTruncated (Classical.choose (homotopyCategory_homMk_surjective _ _
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram_initialVertexIso h x c).hom))

/-- 概要：選んだ辺は、元の降下同型の成分そのものを表す。
方針：辺の選択の等式を回収する。
規約：同型の成分を独立に選び直さない。
使われ方：可逆性と元の coherent な比較の照合。 -/
theorem weakSpanKanQuotientValueEdge_hom :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientValueEdge h x c).toTruncated =
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram_initialVertexIso h x c).hom :=
  Classical.choose_spec (homotopyCategory_homMk_surjective _ _
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram_initialVertexIso h x c).hom)

/-- 概要：商上の小さい実 fiber を元の同じ Kan 図式値へ戻す同値。
方針：小さい fiber 値同値と元の降下同型の実辺を合成する。
規約：商の全関手同型の指定成分を使う。
使われ方：各 fiber の全単体と恒等点の比較。 -/
def weakSpanKanQuotientFiberValueEquivalence :
    QCatEquivalence (vertexFiber
      (smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x))
      (q.hom.app (Opposite.op ⦋0⦌)
        ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c))))
      (((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanDiagram i x).obj c).obj) := by
  let e := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientValueEdge h x c
  have he : IsInvertibleEdge e := by
    change IsIso (Truncated.HomotopyCategory.homMk e.toTruncated)
    rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientValueEdge_hom]
    infer_instance
  exact (smallLeftUnstraighteningFiberValueEquivalence (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x)
    (q.hom.app (Opposite.op ⦋0⦌)
      ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)))).trans
        (F2.Compact.spaceInfinityEdgeValue_isQCatEquivalence e he).choose

/-- 概要：元の各固定 span を商上の小さい fiber へ送る指定単位。
方針：同じ Kan 値への単位に、指定 fiber 値同値の逆を合成する。
規約：可変終点に自然な全族写像とはまだ同定しない。
使われ方：上流の全族構成が回収すべき fiber 制限。 -/
def weakSpanKanQuotientFiberUnit :=
  _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanFiberUnit i x c ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberValueEquivalence h x c).inv

/-- 概要：指定 fiber 単位は元の Kan 置換単位を全体として回収する。
方針：同じ値同値の余単位と元の厳密回収等式を合成する。
規約：全 fiber の関手同型。全族の自然性は仮定しない。
使われ方：K-B-S の fiber 回収条件を明示する。 -/
def weakSpanKanQuotientFiberUnit_recovery : FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit h x c ≫
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberValueEquivalence h x c).hom ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanValueComparison i x c)
    (F2.continuousKanReplacementUnit.app _) := by
  have e := ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberValueEquivalence h x c).invHomIso.precomp
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanFiberUnit i x c)).postcomp (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanValueComparison i x c)
  simpa only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit, Category.assoc, Category.comp_id,
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanFiberUnit_valueComparison] using! e

/-- 概要：底 q を厳密に保つ全族写像の、元の固定 span fiber への実制限。
方針：元の fiber 包含と全族写像を合成し、商上の指定 fiber へ持ち上げる。
規約：全族写像と底の等式が与えられた場合だけの条件付き構成。
使われ方：F1 への不足界面の型と K-B-S の全 fiber 回収条件。 -/
def weakSpanKanQuotientFamilyFiberMap
    (f : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamily B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x ⟶
      smallLeftUnstraightening (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x))
    (hf : f ≫ smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x) =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x ≫ q.hom) :=
  vertexFiberLift (smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x))
    (q.hom.app (Opposite.op ⦋0⦌)
      ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)))
    ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexFiberIso i x c).hom ≫
      (vertexFiberPullbackIso (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x)
        (transportSimplexFirstVertexMap B.obj) (nerveVertex c)).hom ≫
      vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x) _ ≫ f)
    (by
      simp only [Category.assoc, hf]
      rw [← Category.assoc (vertexFiberι _ _), vertexFiberι_comp, SSet.const_comp,
        SSet.comp_const, SSet.comp_const])

/-- 概要：全族写像の fiber 制限は元の固定 span の包含後の像そのもの。
方針：元の pullback fiber 同型の往復を消去する。
規約：全族写像と厳密な底の等式に条件付き。始域の span を選び直さない。
使われ方：指定 fiber 制限が元の全族写像の実制限であることの確認。 -/
theorem weakSpanKanQuotientFamilyFiberMap_inclusion
    (f : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamily B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x ⟶
      smallLeftUnstraightening (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x))
    (hf : f ≫ smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x) =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x ≫ q.hom) :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFiberMap h x c f hf ≫
      vertexFiberι (smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x)) _ =
      fixedMarkedSpanToFamily B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x
        ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)) ≫ f := by
  simp only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFiberMap, vertexFiberLift_ι, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexFiberIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- 概要：元の恒等点を同じ fiber 値同値の逆で運んだ補助点。
方針：既存の strict Kan 恒等点を用いる。
規約：別の恒等 span や新しい Kan 点は選ばない。
使われ方：fiber 単位の計算。既存 weakIdentityQuotientFiberPoint との比較は別条件。 -/
def weakSpanKanQuotientIdentityPoint :=
  (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberValueEquivalence h x
    (transportSimplexIndex (n := ⦋0⦌) x)).inv.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityKanPoint h x)

/-- 概要：指定 fiber 単位の恒等点像は同じ補助 fiber 点に厳密一致。
方針：元の Kan 単位の恒等点計算を後合成する。
規約：fiber 内の等式なので同型も直ちに得られる。
使われ方：K-B-S の恒等 span 照合の中間計算。既存の指定点との同型は未主張。 -/
theorem weakSpanKanQuotientFiberUnit_identity :
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit h x (transportSimplexIndex (n := ⦋0⦌) x)).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityFixedSpanAtZeroIndex h x) =
        _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientIdentityPoint h x := by
  exact congrArg ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberValueEquivalence h x
    (transportSimplexIndex (n := ⦋0⦌) x)).inv.app (Opposite.op ⦋0⦌))
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanFiberUnit_identity i x h)

/-- 概要：全族写像の指定制限に条件付きで、元の Kan 単位を fiber 全体で回収する。
方針：与えられた制限同型を同じ値比較へ後合成する。
規約：全族写像や制限同型の存在を主張する定理ではない。
使われ方：実全族写像の供給後に Sp-6 s4 へ渡す回収条件。 -/
def weakSpanKanQuotientFamilyFiber_recovery
    (f : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamily B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x ⟶
      smallLeftUnstraightening (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x))
    (hf : f ≫ smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x) =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x ≫ q.hom)
    (e : FunctorIso (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFiberMap h x c f hf)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit h x c)) : FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFiberMap h x c f hf ≫
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberValueEquivalence h x c).hom ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanValueComparison i x c)
    (F2.continuousKanReplacementUnit.app _) :=
  e.postcomp _ ≪≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit_recovery h x c

/-- 概要：全族写像の指定制限に条件付きで、恒等 span 像を補助 fiber 点と比較する。
方針：全 fiber 制限同型の恒等 span 成分と同じ指定点等式を合成する。
規約：商の全空間の同型だけで fiber 内同型を代用しない。
使われ方：K-B-S の恒等点条件の中間比較。既存の指定点との照合は別途必要。 -/
def weakSpanKanQuotientFamily_identityIso
    (f : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamily B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x ⟶
      smallLeftUnstraightening (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x))
    (hf : f ≫ smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x) =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x ≫ q.hom)
    (e : FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFiberMap h x (transportSimplexIndex (n := ⦋0⦌) x) f hf)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit h x (transportSimplexIndex (n := ⦋0⦌) x))) :
    VertexIso
      ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFiberMap h x (transportSimplexIndex (n := ⦋0⦌) x) f hf).app
        (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityFixedSpanAtZeroIndex h x))
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientIdentityPoint h x) :=
  e.app _ ≪≫ eqToIso (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit_identity h x))

/-- 概要：底 q を厳密に保つ実全族写像の恒等 span 像を、元の q(x) fiber で読む。
方針：同じ零単体添字の初頂点等式で fiber の表示だけを移す。
規約：全族写像と底の等式に条件付き。元の指定恒等点への同型はまだ仮定しない。
使われ方：Sp-6 s4 の weakIdentityQuotientFiberPoint との比較の正確な始域。 -/
def weakSpanKanQuotientFamilyIdentityImage
    (f : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamily B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x ⟶
      smallLeftUnstraightening (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x))
    (hf : f ≫ smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x) =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x ≫ q.hom) :
    (vertexFiber (smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x))
      (q.hom.app (Opposite.op ⦋0⦌) x)) _⦋0⦌ :=
  (eqToHom (congrArg
    (vertexFiber (smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x)))
    (congrArg (q.hom.app (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex x)))).app
    (Opposite.op ⦋0⦌)
    ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFiberMap h x (transportSimplexIndex (n := ⦋0⦌) x) f hf).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityFixedSpanAtZeroIndex h x))

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFiberMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFiberMap := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFiberMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFiberMap_inclusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFiberMap_inclusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFiber_recovery (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFiber_recovery := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFiber_recovery

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyIdentityImage (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyIdentityImage := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyIdentityImage

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamily_identityIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamily_identityIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamily_identityIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFiberUnit := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFiberUnit_identity := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit_identity

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit_recovery (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFiberUnit_recovery := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit_recovery

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberValueEquivalence (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFiberValueEquivalence := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberValueEquivalence

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientIdentityPoint (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientIdentityPoint := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientIdentityPoint

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientValueEdge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientValueEdge := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientValueEdge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientValueEdge_hom := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientValueEdge_hom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFiberMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFiberMap._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFiberMap._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFiberMap._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFiberMap.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFiberMap.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyIdentityImage._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyIdentityImage._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamily_identityIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamily_identityIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamily_identityIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamily_identityIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFiberUnit.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFiberUnit_recovery._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit_recovery._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFiberUnit_recovery._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit_recovery._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFiberUnit_recovery._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit_recovery._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFiberUnit_recovery._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit_recovery._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFiberUnit_recovery._proof_5 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit_recovery._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFiberUnit_recovery._proof_6 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit_recovery._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFiberUnit_recovery._proof_7 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit_recovery._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFiberUnit_recovery._proof_8 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberUnit_recovery._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFiberValueEquivalence._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberValueEquivalence._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFiberValueEquivalence._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberValueEquivalence._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFiberValueEquivalence._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberValueEquivalence._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFiberValueEquivalence._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberValueEquivalence._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFiberValueEquivalence._proof_5 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberValueEquivalence._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFiberValueEquivalence._proof_6 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberValueEquivalence._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientIdentityPoint._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientIdentityPoint._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientIdentityPoint._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientIdentityPoint._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientValueEdge._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientValueEdge._proof_1
