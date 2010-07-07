-- relation schema: name -> type

data BaseType = STRING | INTEGER
data BaseData = BaseString [Char] | BaseInteger Integer

data ColumnName  = ColumnName [Char]
                deriving Show

type Schema = ColumnName -> BaseType

baseTypeChecker :: BaseType -> BaseData -> Bool
baseTypeChecker STRING (BaseString _) = True
baseTypeChecker INTEGER (BaseInteger _) = True
baseTypeChecker _ _ = False

type Row = RowName -> BaseData
type Data = [Row]

-- sort
-- filter
-- SQL interpreter 