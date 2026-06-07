# mdict_cgi
MDict CGI dictionary client

## Configuration
Set the path containing` .mdx/.mdd` dictionary files in the file `config.py`, e.g.

```sh
DICT_DIR = "~/Dictionaries"
```

## Run
```sh
python3 cgi-server.py
```

Override the path to MDict dictionaries via env var (takes precedence over `config.py`):

```sh
DICT_DIR="~/path/to/custom/dictionaries" SERVER_PORT=8888 python3 cgi-server.py
```

Open in browser:

- http://localhost:8808/cgi-bin/mdict_cgi.py
