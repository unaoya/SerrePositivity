module
public import SerrePositivity.InfinityCategories.Derived.FullCofiberVertices
public import SerrePositivity.InfinityCategories.Derived.MappingConeZeroTarget
public import SerrePositivity.InfinityCategories.Derived.StableHomotopyComparison

/-! # Semifree の標準 suspension 四角形

概要：零写像の span から実際の suspension 四角形を作り、終点を複体シフトと同定する。
方針：Semifree の標準 cofiber と四頂点の式、零終域の cone 接続同型を使う。
規約：接続同型は Mathlib の符号を保つ。使われ方：D7 の suspension 比較の具体的な模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve CochainComplex
open scoped Simplicial ZeroObject
variable {S : Type u} [CommRing S]

/-- Semifree 複体 X の標準 suspension 四角形。 -/
def semifreeSuspensionSquare (X : Semifree S) :
    SuspensionSquare (X := derivedInfinityCategory S) (Simplex.vertex X) where
  square := semifreeCofiberSquare (0 : X.val ⟶ 0) (0 : X.val ⟶ 0)
    X.property (complexSemifree_zero S) (complexSemifree_zero S)
  source_eq := fullCofiberSquare_vertex00 _ _ _ _ _ _ _
  zero_corner := by
    rw [semifreeCofiberSquare, fullCofiberSquare_vertex01]
    exact derivedInfinityZeroVertex_isZeroVertex S
  other_zero := by
    rw [semifreeCofiberSquare, fullCofiberSquare_vertex10]
    exact derivedInfinityZeroVertex_isZeroVertex S
  isPushout := semifreeCofiberSquare_isPushout _ _ _ _ _

/-- 標準 suspension の終点を表す Semifree 複体。 -/
def semifreeSuspensionObject (X : Semifree S) : Semifree S :=
  ⟨pushoutCofiber (0 : X.val ⟶ 0) (0 : X.val ⟶ 0),
    complexSemifree_pushoutCofiber _ _ X.property
      (complexSemifree_zero S) (complexSemifree_zero S)⟩

/-- 標準 suspension 四角形の終点は標準 cone の頂点。 -/
lemma semifreeSuspensionSquare_vertex (X : Semifree S) :
    (semifreeSuspensionSquare X).vertex = Simplex.vertex (semifreeSuspensionObject X) :=
  fullCofiberSquare_vertex11 _ _ _ _ _ _ _

/-- 標準 suspension の複体は元の複体の一回シフトと同型。 -/
def semifreeSuspensionComplexIso (X : Semifree S) :
    (semifreeSuspensionObject X).val ≅ X.val⟦(1 : ℤ)⟧ :=
  mappingConeZeroTargetIso _ ((biprod_isZero_iff (0 : Complex S) 0).mpr
    ⟨isZero_zero _, isZero_zero _⟩)

/-- 鎖写像から標準 suspension の複体間の射を作る。 -/
def semifreeSuspensionComplexMap {X Y : Semifree S} (a : X.val ⟶ Y.val) :
    (semifreeSuspensionObject X).val ⟶ (semifreeSuspensionObject Y).val :=
  mappingCone.map _ _ a (𝟙 _) (by simp [cofiberDifference, biprod.lift_eq])

/-- 標準 suspension の複体シフト比較は鎖写像に対して自然。 -/
lemma semifreeSuspensionComplexIso_naturality {X Y : Semifree S} (a : X.val ⟶ Y.val) :
    semifreeSuspensionComplexMap a ≫ (semifreeSuspensionComplexIso Y).hom =
      (semifreeSuspensionComplexIso X).hom ≫ a⟦(1 : ℤ)⟧' :=
  mappingConeZeroTargetIso_naturality _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories
