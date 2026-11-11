module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：単体集合の反転によるホーンと辺の双対化。
方針：Mathlib の opFunctor と標準単体の反転同型を部分複体の逆像に制限する。
規約：反転は圏の反変関手ではなく単体集合の共変な involution。
使われ方：HTT Proposition 1.2.4.3 の双対、Kerodon Theorem 4.4.2.6（Tag 019F）。

対応節は Kerodon 1.4（Tag 0039）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories

/-- 概要：部分複体の反転は反転した単体集合の部分複体と同型。
方針：各次数の部分型を恒等写像で同定する。
規約：周囲の包含と可換な同型を取る。
使われ方：Kerodon §4.4（Tag 01EM）、ホーンを反転して充填する際の型の整合。 -/
def subcomplexOppositeIso {X : SSet.{u}} (A : X.Subcomplex) :
    (A : SSet.{u}).op ≅ (A.op : SSet.{u}) :=
  NatIso.ofComponents (fun _ ↦ (Equiv.refl _).toIso) (fun _ ↦ by rfl)

/-- 概要：部分複体の反転の同型は包含と可換。
方針：全ての成分で同じ部分型の値を取る。
規約：右辺は opFunctor で写した包含。
使われ方：Kerodon §4.4（Tag 01EM） のホーンの反転。 -/
lemma subcomplexOppositeIso_hom_ι {X : SSet.{u}} (A : X.Subcomplex) :
    (subcomplexOppositeIso A).hom ≫ A.op.ι = SSet.opFunctor.map A.ι := rfl

/-- 概要：添字を反転したホーンは元のホーンの反転と同型。
方針：標準単体の反転同型でホーンの部分複体を引き戻す。
規約：次数は任意で、外側・内側の全てのホーンを含む。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の左右の双対。 -/
@[kerodon 003S]
def hornReverseIso (n : ℕ) (i : Fin (n + 1)) :
    (horn n i.rev : SSet.{u}) ≅ (horn n i : SSet.{u}).op :=
  Subcomplex.eqToIso (op_horn i).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.subcomplexPreimageIso (horn n i).op (stdSimplex.opIso ⦋n⦌).symm ≪≫
    (subcomplexOppositeIso (horn n i)).symm

/-- 概要：反転ホーンの同型は反転した標準単体への包含と可換。
方針：部分複体の逆像の同型の可換性を計算する。
規約：標準単体の反転同型の逆射を使う。
使われ方：HTT Proposition 1.2.4.3 の双対への充填の移送。 -/
lemma hornReverseIso_hom_ι (n : ℕ) (i : Fin (n + 1)) :
    (hornReverseIso.{u} n i).hom ≫ SSet.opFunctor.map (horn n i).ι =
      (horn n i.rev).ι ≫ (stdSimplex.opIso ⦋n⦌).inv := by
  rw [← subcomplexOppositeIso_hom_ι]
  change ((Subcomplex.homOfLE (op_horn i).symm.le ≫
    (horn n i).op.fromPreimage (stdSimplex.opIso ⦋n⦌).inv) ≫
    (subcomplexOppositeIso (horn n i)).inv) ≫
      (subcomplexOppositeIso (horn n i)).hom ≫ _ = _
  rw [Category.assoc, Iso.inv_hom_id_assoc, Category.assoc,
    Subcomplex.fromPreimage_ι, ← Category.assoc, Subcomplex.homOfLE_ι]

/-- 概要：標準単体の反転を二度適用すると恒等。
方針：有限順序集合の添字と値の反転を二度計算する。
規約：opFunctor の involution の同型も合成に含める。
使われ方：Kerodon §4.4（Tag 01EM）、双対化した充填を元へ戻す計算。 -/
lemma stdSimplex_doubleReverse (n : ℕ) :
    (stdSimplex.opIso.{u} ⦋n⦌).inv ≫ SSet.opFunctor.map (stdSimplex.opIso ⦋n⦌).inv ≫
      (SSet.opFunctorCompOpFunctorIso.app (Δ[n] : SSet.{u})).hom = 𝟙 Δ[n] := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply stdSimplex.ext
  intro i
  change ((a i.rev.rev).rev).rev = a i
  simp

/-- 概要：quasicategory を反転しても quasicategory。
方針：内ホーンを反転同型で移し、元の充填を反転して戻す。
規約：モデル構造は使わず、内ホーンの充填だけを用いる。
使われ方：HTT Proposition 1.2.4.3、Kerodon Theorem 4.4.2.6（Tag 019F） の左右の対称性。 -/
@[kerodon 003S]
instance quasicategory_op (X : SSet.{u}) [Quasicategory X] : Quasicategory X.op where
  hornFilling' {n i} σ h₀ hlast := by
    let τ : (horn (n + 2) i.rev : SSet.{u}) ⟶ X :=
      (hornReverseIso (n + 2) i).hom ≫ SSet.opFunctor.map σ ≫
      (SSet.opFunctorCompOpFunctorIso.app X).hom
    have hi₀ : (0 : Fin (n + 3)) < i.rev := by
      change 0 < i.rev.val
      rw [Fin.val_rev]
      have hi : i.val < n + 2 := hlast
      omega
    have hilast : i.rev < Fin.last (n + 2) := by
      change i.rev.val < n + 2
      rw [Fin.val_rev]
      have hi : 0 < i.val := h₀
      omega
    obtain ⟨F, hF⟩ := Quasicategory.hornFilling (S := X) hi₀ hilast τ
    let G := (stdSimplex.opIso ⦋n + 2⦌).inv ≫ SSet.opFunctor.map F
    refine ⟨G, ?_⟩
    have : SSet.opFunctor.{u}.Faithful := SSet.opEquivalence.faithful_functor
    apply SSet.opFunctor.map_injective
    apply (cancel_epi (hornReverseIso (n + 2) i).hom).1
    apply (cancel_mono (SSet.opFunctorCompOpFunctorIso.app X).hom).1
    change τ = ((hornReverseIso (n + 2) i).hom ≫
      SSet.opFunctor.map ((horn (n + 2) i).ι ≫ G)) ≫
        (SSet.opFunctorCompOpFunctorIso.app X).hom
    have hn : SSet.opFunctor.map (SSet.opFunctor.map F) ≫
        (SSet.opFunctorCompOpFunctorIso.app X).hom =
        (SSet.opFunctorCompOpFunctorIso.app (Δ[n + 2] : SSet.{u})).hom ≫ F := by
      exact (SSet.opFunctorCompOpFunctorIso.hom.naturality F)
    dsimp only [G]
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      ← Category.assoc, hornReverseIso_hom_ι]
    simp only [Category.assoc]
    rw [hn, ← Category.assoc (SSet.opFunctor.map (stdSimplex.opIso ⦋n + 2⦌).inv)
      (SSet.opFunctorCompOpFunctorIso.app (Δ[n + 2] : SSet.{u})).hom F,
      ← Category.assoc (stdSimplex.opIso ⦋n + 2⦌).inv
        (SSet.opFunctor.map (stdSimplex.opIso ⦋n + 2⦌).inv ≫
          (SSet.opFunctorCompOpFunctorIso.app (Δ[n + 2] : SSet.{u})).hom) F,
      stdSimplex_doubleReverse, Category.id_comp]
    exact hF

/-- 概要：辺を反転して向きの逆な辺にする。
方針：一単体は opObjEquiv で移し、両端が反転する面の式を使う。
規約：始点と終点を交換する。
使われ方：Kerodon §4.4（Tag 01EM）、左右の外側ホーンの固定する辺の対応。 -/
def edgeOp {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    SSet.Truncated.Edge (X := (truncation 2).obj X.op)
      (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x) where
  edge := SSet.opObjEquiv.symm e.edge
  src_eq := by
    change X.op.δ 1 (SSet.opObjEquiv.symm e.edge) = _
    rw [SSet.op_δ]
    exact congrArg SSet.opObjEquiv.symm e.tgt_eq
  tgt_eq := by
    change X.op.δ 0 (SSet.opObjEquiv.symm e.edge) = _
    rw [SSet.op_δ]
    exact congrArg SSet.opObjEquiv.symm e.src_eq

/-- 概要：反転は恒等辺を保つ。
方針：零番目の退化の反転を計算する。
規約：頂点は opObjEquiv で移す。
使われ方：Kerodon §4.4（Tag 01EM）、反転による逆三角形の移送。 -/
lemma edgeOp_id {X : SSet.{u}} (x : X _⦋0⦌) :
    edgeOp (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x) =
      SSet.Truncated.Edge.id (X := (truncation 2).obj X.op) (SSet.opObjEquiv.symm x) := by
  apply SSet.Truncated.Edge.ext
  change SSet.opObjEquiv.symm (X.σ 0 x) = X.op.σ 0 (SSet.opObjEquiv.symm x)
  rw [SSet.op_σ]
  rfl

/-- 概要：合成三角形の反転は逆順の合成三角形。
方針：二単体を反転し、零番目と二番目の面を交換する。
規約：対角の辺も反転する。
使われ方：Kerodon §4.4（Tag 01EM）、辺の可逆性の双対不変性。 -/
def compStructOp {X : SSet.{u}} {x y z : X _⦋0⦌}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    {g : SSet.Truncated.Edge (X := (truncation 2).obj X) y z}
    {h : SSet.Truncated.Edge (X := (truncation 2).obj X) x z}
    (t : SSet.Truncated.Edge.CompStruct f g h) :
    SSet.Truncated.Edge.CompStruct (edgeOp g) (edgeOp f) (edgeOp h) where
  simplex := SSet.opObjEquiv.symm t.simplex
  d₂ := by
    change X.op.δ 2 (SSet.opObjEquiv.symm t.simplex) = SSet.opObjEquiv.symm g.edge
    rw [SSet.op_δ]
    exact congrArg SSet.opObjEquiv.symm t.d₀
  d₀ := by
    change X.op.δ 0 (SSet.opObjEquiv.symm t.simplex) = SSet.opObjEquiv.symm f.edge
    rw [SSet.op_δ]
    exact congrArg SSet.opObjEquiv.symm t.d₂
  d₁ := by
    change X.op.δ 1 (SSet.opObjEquiv.symm t.simplex) = SSet.opObjEquiv.symm h.edge
    rw [SSet.op_δ]
    exact congrArg SSet.opObjEquiv.symm t.d₁

/-- 概要：可逆な辺を反転しても可逆。
方針：両側逆の二つの三角形を反転する。
規約：反転先の可逆性はそのホモトピー圏での可逆性。
使われ方：HTT Proposition 1.2.4.3、Kerodon Theorem 4.4.2.6（Tag 019F） の双対。 -/
lemma IsInvertibleEdge.op {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := X.op) (edgeOp e) := by
  obtain ⟨g, t₁, t₂⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge.nonempty_inverse he
  have h₁ : SSet.Truncated.Edge.CompStruct (edgeOp e) (edgeOp g)
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X.op) (SSet.opObjEquiv.symm y)) := by
    rw [← edgeOp_id]
    exact compStructOp t₂
  have h₂ : SSet.Truncated.Edge.CompStruct (edgeOp g) (edgeOp e)
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X.op) (SSet.opObjEquiv.symm x)) := by
    rw [← edgeOp_id]
    exact compStructOp t₁
  refine ⟨⟨SSet.Truncated.HomotopyCategory.homMk (edgeOp g), ?_, ?_⟩⟩
  · simpa using SSet.Truncated.HomotopyCategory.homMk_comp_homMk h₁
  · simpa using SSet.Truncated.HomotopyCategory.homMk_comp_homMk h₂

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge export _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.IsInvertibleEdge (op)


/-- 概要：反転した辺の可逆性と元の辺の可逆性は同値。
方針：反転を二度適用し、opFunctor の involution の同型で戻す。
規約：仮定は元の quasicategory 性のみ。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の左右の同値の移送。 -/
lemma isInvertibleEdge_op_iff {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := X.op) (edgeOp e) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  constructor
  · intro h
    have h' := IsInvertibleEdge.op (X := X.op) h
    have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge.map (X := X.op.op) (Y := X) h'
      (SSet.opFunctorCompOpFunctorIso.app X).hom
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (f := e) rfl).1 hm
  · exact IsInvertibleEdge.op

/-- 概要：標準単体からの射を反転する。
方針：標準単体の反転同型の逆射で前合成する。
規約：標準単体の次数は変えない。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の充填の双対化。 -/
def reverseSimplex {X : SSet.{u}} (n : ℕ) (F : (Δ[n] : SSet.{u}) ⟶ X) :
    (Δ[n] : SSet.{u}) ⟶ X.op :=
  (stdSimplex.opIso ⦋n⦌).inv ≫ SSet.opFunctor.map F

/-- 概要：単体の反転は標的での後合成と可換。
方針：opFunctor の合成保存を使う。
規約：標的の射は任意。
使われ方：Kerodon §4.4（Tag 01EM） の反転からの復帰。 -/
lemma reverseSimplex_comp {X Y : SSet.{u}} (n : ℕ) (F : (Δ[n] : SSet.{u}) ⟶ X)
    (q : X ⟶ Y) : reverseSimplex n (F ≫ q) = reverseSimplex n F ≫ SSet.opFunctor.map q := by
  simp only [reverseSimplex, CategoryTheory.Functor.map_comp, Category.assoc]

/-- 概要：opFunctor の二重反転の同型は反転自身と可換。
方針：成分は全て恒等写像であることを計算する。
規約：二つの自然同型の対象は同じ三重反転。
使われ方：Kerodon §4.4（Tag 01EM）、二重反転した充填の整合。 -/
lemma opFunctorCompOpFunctorIso_coherence (X : SSet.{u}) :
    SSet.opFunctor.map (SSet.opFunctorCompOpFunctorIso.app X).hom =
      (SSet.opFunctorCompOpFunctorIso.app X.op).hom := rfl

/-- 概要：単体を二度反転し、標的の同型で戻すと元の単体。
方針：二重反転の自然性と標準単体の二重反転の計算を使う。
規約：標的に quasicategory 性は不要。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の双対化の逆関係。 -/
lemma reverseSimplex_double {X : SSet.{u}} (n : ℕ) (F : (Δ[n] : SSet.{u}) ⟶ X) :
    reverseSimplex n (reverseSimplex n F) ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom = F := by
  have hn : SSet.opFunctor.map (SSet.opFunctor.map F) ≫
      (SSet.opFunctorCompOpFunctorIso.app X).hom =
      (SSet.opFunctorCompOpFunctorIso.app (Δ[n] : SSet.{u})).hom ≫ F :=
    SSet.opFunctorCompOpFunctorIso.hom.naturality F
  dsimp only [reverseSimplex]
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [hn, ← Category.assoc (SSet.opFunctor.map (stdSimplex.opIso ⦋n⦌).inv)
      (SSet.opFunctorCompOpFunctorIso.app (Δ[n] : SSet.{u})).hom F,
    ← Category.assoc (stdSimplex.opIso ⦋n⦌).inv
      (SSet.opFunctor.map (stdSimplex.opIso ⦋n⦌).inv ≫
        (SSet.opFunctorCompOpFunctorIso.app (Δ[n] : SSet.{u})).hom) F,
    stdSimplex_doubleReverse, Category.id_comp]

/-- 概要：反転した標的への単体を戻してから反転すると元に戻る。
方針：後合成との可換性、二重反転の同型の整合、二重反転の計算を使う。
規約：標的の元の単体集合 X を指定する。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の充填の反映。 -/
lemma reverseSimplex_back {X : SSet.{u}} (n : ℕ) (F : (Δ[n] : SSet.{u}) ⟶ X.op) :
    reverseSimplex n (reverseSimplex n F ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom) = F := by
  rw [reverseSimplex_comp, opFunctorCompOpFunctorIso_coherence, reverseSimplex_double]

/-- 概要：ホーンからの射を反転する。
方針：反転ホーンの同型で opFunctor の像に前合成する。
規約：欠ける面の添字も反転する。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の左右の条件の対応。 -/
def reverseHornMap {X : SSet.{u}} (n : ℕ) (i : Fin (n + 1))
    (σ : (horn n i : SSet.{u}) ⟶ X) : (horn n i.rev : SSet.{u}) ⟶ X.op :=
  (hornReverseIso n i).hom ≫ SSet.opFunctor.map σ

/-- 概要：ホーンへの制限と反転は可換。
方針：ホーンの反転同型と包含の可換性を使う。
規約：反転した辺や単体を取り替えない。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の充填の移送。 -/
lemma reverseHornMap_restrict {X : SSet.{u}} (n : ℕ) (i : Fin (n + 1))
    (F : (Δ[n] : SSet.{u}) ⟶ X) :
    reverseHornMap n i ((horn n i).ι ≫ F) = (horn n i.rev).ι ≫ reverseSimplex n F := by
  dsimp only [reverseHornMap, reverseSimplex]
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc, hornReverseIso_hom_ι, Category.assoc]

/-- 概要：ホーンからの射の反転は単射。
方針：前合成の同型と opFunctor の忠実性で等式を反映する。
規約：quasicategory 性は不要。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の充填を元へ戻す手順。 -/
lemma reverseHornMap_injective (X : SSet.{u}) (n : ℕ) (i : Fin (n + 1)) :
    Function.Injective (reverseHornMap (X := X) n i) := by
  intro a b h
  have : SSet.opFunctor.{u}.Faithful := SSet.opEquivalence.faithful_functor
  apply SSet.opFunctor.map_injective
  exact (cancel_epi (hornReverseIso n i).hom).1 h

/-- 概要：反転したホーンが充填できれば元のホーンも充填できる。
方針：充填を反転して標的の同型で戻し、反転写像の単射性で境界の式を確かめる。
規約：両側とも同じ次数と指定した境界のまま。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の双対への帰着。 -/
lemma hornFiller_of_reverseHornFiller {X : SSet.{u}} (n : ℕ) (i : Fin (n + 1))
    (σ : (horn n i : SSet.{u}) ⟶ X) (F : (Δ[n] : SSet.{u}) ⟶ X.op)
    (hF : (horn n i.rev).ι ≫ F = reverseHornMap n i σ) :
    ∃ G : (Δ[n] : SSet.{u}) ⟶ X, (horn n i).ι ≫ G = σ := by
  refine ⟨reverseSimplex n F ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom, ?_⟩
  apply reverseHornMap_injective X n i
  rw [reverseHornMap_restrict, reverseSimplex_back]
  exact hF

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
